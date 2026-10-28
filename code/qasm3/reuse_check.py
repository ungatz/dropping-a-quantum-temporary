"""Compare fresh and reused DQT compilations as quantum channels.

The checker consumes the compiler's stdout directly.  It keeps the lift
measurements, removes only the final ``result`` measurements, and compares
the unnormalised channel contribution of each lift record after tracing out
hidden temporaries.  Input and loan wires are entangled with reference wires;
this makes the comparison sensitive to every input, including dirty loans.
"""
import argparse
import itertools
import json
import math
import os
import subprocess
import sys

import numpy as np
import openqasm3
from openqasm3 import ast as qast

import compile_check as sim

TOL = 1e-9
ADMITTED_PROGRAMS = (
    "two-phases.s", "two-phases-uncompute.s", "grover-two-rounds.s", "measured-and-twice.s",
    "mcx-dirty-x.s", "bell-pair.s", "bell-pair-split.s",
    "c-decomposed.s", "c-exposed.s", "c-witness.s", "a-then-u.s",
)


def result_measurements(program):
    """Remove terminal output measurements after validating their bit indices."""
    reads, kept = [], []
    terminal = False
    for statement in program.body:
        if isinstance(statement, qast.QuantumMeasurementStatement):
            reg, bit = sim.resolve_bit_target(statement.target, program.creg_sizes)
            if reg == "result":
                terminal = True
                reads.append((bit, sim.qubit_index(statement.measure.qubit)))
                continue
        if terminal:
            raise ValueError("result measurements must be terminal")
        kept.append(statement)
    indices = [bit for bit, _ in reads]
    if sorted(indices) != list(range(program.creg_sizes.get("result", 0))):
        raise ValueError("result measurements omit or duplicate a bit")
    program.body = kept
    return tuple(q for _, q in sorted(reads))


def validate_allocation(data, program, mode):
    """Validate the supported finite basis-allocation slice and return maps."""
    if not isinstance(data, dict) or not isinstance(data.get("wires"), list):
        raise ValueError("allocation report has no wires")
    qfield = "fresh" if mode == "fresh" else "reuse"
    width = int(data["freshQubits"] if mode == "fresh" else data["reuseQubits"])
    if width < 0 or program.nq != width:
        raise ValueError(f"{mode} allocation width {width} does not match QASM width {program.nq}")
    if not data["wires"] and width != 0:
        raise ValueError("allocation report has no wires")
    permanent = set()
    temporary_qubits = set()
    wire_by_name = {}
    input_qubits = []
    loan_qubits = []
    temp_bits = {}
    for wire in data["wires"]:
        name = wire["name"]
        if name in wire_by_name:
            raise ValueError("duplicate register name in allocation report")
        qs = [int(q) for q in wire[qfield]]
        if not qs or len(set(qs)) != len(qs):
            raise ValueError(f"wire {name} has an empty or duplicate qubit mapping")
        if any(q < 0 or q >= width for q in qs):
            raise ValueError(f"wire {name} has an out-of-range mapping")
        wire_by_name[name] = qs
        kind = wire["kind"]
        if kind == "input":
            if permanent.intersection(qs):
                raise ValueError(f"permanent wire {name} overlaps another permanent wire")
            permanent.update(qs)
            input_qubits.extend(qs)
        elif kind == "loan":
            if permanent.intersection(qs):
                raise ValueError(f"permanent wire {name} overlaps another permanent wire")
            permanent.update(qs)
            loan_qubits.extend(qs)
        elif kind == "temporary":
            basis = wire.get("basis")
            if basis is None:
                raise ValueError(f"non-basis temporary allocation for {name} is unsupported")
            basis = int(basis)
            if not 0 <= basis < 2 ** len(qs):
                raise ValueError(f"basis allocation for {name} is outside its wire width")
            # Scratch storage is always initialized to |0>.  The emitted
            # circuit itself prepares a nonzero basis allocation, including
            # at a reused lifetime; pre-seeding here would prepare it twice.
            temporary_qubits.update(qs)
        else:
            raise ValueError(f"unsupported wire kind {kind!r} for {name}")
    if permanent.intersection(temporary_qubits):
        raise ValueError("temporary mapping overlaps a permanent wire")
    return width, wire_by_name, input_qubits, loan_qubits, temp_bits


def initial_state(width, input_qubits, loan_qubits, temp_bits):
    """Bell-pair every input/loan qubit with a reference; fresh scratch is zero."""
    system = sorted(input_qubits + loan_qubits)
    if len(set(system)) != len(system):
        raise ValueError("input and loan mappings overlap")
    nref = len(system)
    state = np.zeros((2,) * (width + nref), dtype=complex)
    scale = 1 / math.sqrt(2 ** nref)
    for label in range(2 ** nref):
        bits = [(label >> (nref - i - 1)) & 1 for i in range(nref)]
        index = [0] * (width + nref)
        for q, bit in temp_bits.items():
            index[q] = bit
        for i, q in enumerate(system):
            index[q] = bits[i]
            index[width + i] = bits[i]
        state[tuple(index)] = scale
    return state


def record_key(record):
    return tuple(sorted((str(name), int(bit)) for name, bit in record))


def all_records(data):
    # A site reports only the lifts in scope there.  The channel contribution
    # is indexed by the complete run record, so join all lift bits globally.
    lifts = data.get("lifts", [])
    names = [entry["name"] for entry in lifts]
    if not names:
        return [[]]
    return [list(zip(names, values)) for values in itertools.product((0, 1), repeat=len(names))]


def statement_counts(statements):
    gates = measurements = 0
    for statement in statements:
        if isinstance(statement, (qast.QuantumGate, qast.QuantumPhase)):
            gates += 1
        elif isinstance(statement, qast.QuantumMeasurementStatement):
            measurements += 1
        elif isinstance(statement, qast.BranchingStatement):
            g, m = statement_counts(statement.if_block)
            gates += g
            measurements += m
            if statement.else_block is not None:
                g, m = statement_counts(statement.else_block)
                gates += g
                measurements += m
    return gates, measurements


def branch_matches(bits, record, lifts):
    for name, value in record:
        if name not in lifts:
            raise ValueError(f"record refers to unknown lift {name}")
        bit_index, survived_value = lifts[name]
        got = bits.get(("c", bit_index))
        want = survived_value if int(value) else 1 - survived_value
        if got != want:
            return False
    return True


def reduced_density(state, keep_qubits, total_qubits):
    keep = list(keep_qubits)
    if len(set(keep)) != len(keep):
        raise ValueError("output mapping contains duplicate qubits")
    hidden = [q for q in range(total_qubits) if q not in keep]
    tensor = np.transpose(state, keep + hidden)
    matrix = tensor.reshape(2 ** len(keep), 2 ** len(hidden))
    return matrix @ matrix.conj().T


def channel_records(qasm_text, data, mode):
    ast = openqasm3.parse(qasm_text)
    program = sim.Program(ast)
    terminal_reads = result_measurements(program)
    gate_count, lift_measurement_count = statement_counts(program.body)
    width, wire_map, inputs, loans, temp_bits = validate_allocation(data, program, mode)
    nref = len(inputs) + len(loans)
    program.nq = width + nref
    lifts = {e["name"]: (int(e["bit"]), int(e["survivedValue"])) for e in data.get("lifts", [])}
    state0 = initial_state(width, inputs, loans, temp_bits)
    branches = program.run_stmts(program.body, state0, {})
    results = {}
    returns = data.get("returns", [])
    if not returns:
        raise ValueError("allocation report has no return mapping")
    # This supported suite has a fixed returned tuple across records.
    return_tuples = {tuple(map(str, item)) for item in returns}
    if len(return_tuples) != 1:
        raise ValueError("record-dependent return mappings are unsupported")
    return_names = next(iter(return_tuples))
    if len(set(return_names)) != len(return_names) or any(n not in wire_map for n in return_names):
        raise ValueError("return metadata contains duplicate or unmapped wire names")
    returned = tuple(q for name in return_names for q in wire_map[name])
    if program.creg_sizes.get("result", 0) != len(returned):
        raise ValueError(
            f"result register has width {program.creg_sizes.get('result', 0)}, "
            f"return metadata maps {len(returned)} qubits"
        )
    if terminal_reads != returned:
        raise ValueError(f"result measures {terminal_reads}, return metadata maps {returned}")
    for record in all_records(data):
        # Lift records select the branch; returned wires come from the explicit
        # return tuple, which is independent of which temporary was dropped.
        names = [str(n) for n, _ in record]
        if any(n not in lifts for n in names):
            raise ValueError(f"record contains an unknown lift name: {names}")
        keep = list(returned) + loans + list(range(width, width + nref))
        rho = None
        for state, bits in branches:
            if not branch_matches(bits, record, lifts):
                continue
            part = reduced_density(state, keep, width + nref)
            rho = part if rho is None else rho + part
        if rho is None:
            rho = np.zeros((2 ** len(keep), 2 ** len(keep)), dtype=complex)
        results[record_key(record)] = rho
    return results, gate_count, lift_measurement_count, len(terminal_reads)


# Convenient integration API for checkpoint tools sharing this file.
def load_case(executable, source):
    fresh_text = run_command(executable, "compile", source)
    reuse_text = run_command(executable, "compile-reuse", source)
    metadata = json.loads(run_command(executable, "allocation", source))
    return metadata, fresh_text, reuse_text


def channels(text, metadata, mode):
    return channel_records(text, metadata, mode)


def compare_channels(fresh, reuse):
    if not fresh or not reuse:
        raise ValueError("channel comparison has no records")
    if set(fresh) != set(reuse):
        return False, float("inf"), "fresh and reuse record sets differ"
    deviation = 0.0
    for record in fresh:
        if fresh[record].shape != reuse[record].shape:
            return False, float("inf"), f"record {record}: output dimensions differ"
        if not np.all(np.isfinite(fresh[record])) or not np.all(np.isfinite(reuse[record])):
            raise ValueError("non-finite channel matrix")
        deviation = max(deviation, float(np.max(np.abs(fresh[record] - reuse[record]))))
    return deviation <= TOL, deviation, ""


def expected_channel(data, source_name):
    """Independent expected maps, converted to numerical Choi densities."""
    if source_name in {"c-decomposed.s", "c-exposed.s", "c-witness.s"}:
        safe = np.array([[1, 1], [0, 0]]) / np.sqrt(2)
        if source_name == "c-decomposed.s":
            maps = {1: [safe], 0: [np.array([[1, -1], [0, 0]]) / 2,
                                   np.array([[0, 0], [1, -1]]) / 2]}
        else:
            safe = np.vstack([safe, np.zeros((2, 2))])
            unsafe = np.zeros((4, 2))
            if source_name == "c-exposed.s":
                unsafe[1] = unsafe[2] = np.array([1, -1]) / 2
            else:
                unsafe[1] = np.array([1, -1]) / np.sqrt(2)
            maps = {1: [safe], 0: [unsafe]}
        return {(("p", bit),): sum(np.outer(k.reshape(-1), k.reshape(-1).conj()) / 2
                                   for k in matrices) for bit, matrices in maps.items()}
    if source_name == "a-then-u.s":
        # v is returned unchanged beside u in |1>: the Choi vector is
        # sum_b |b>_v |1>_u |b>_ref / sqrt 2, in the order (returned, reference).
        vector = np.zeros(8, dtype=complex)
        for b in (0, 1):
            vector[(b << 2) | (1 << 1) | b] = 1 / np.sqrt(2)
        return {(): np.outer(vector, vector.conj())}
    if source_name == "grover-two-rounds.s":
        h = np.array([[1, 1], [1, -1]]) / np.sqrt(2)
        diffusion = np.full((4, 4), 0.5) - np.eye(4)
        oracle = np.diag([1, 1, 1, -1])
        unitary = diffusion @ oracle @ diffusion @ oracle @ np.kron(h, h)
        vector = unitary.reshape(-1) / 2
        return {(): np.outer(vector, vector.conj())}
    if source_name not in {"two-phases.s", "two-phases-uncompute.s", "measured-and-twice.s", "mcx-dirty-x.s", "bell-pair.s", "bell-pair-split.s"}:
        return None
    wire_map = {wire["name"]: [int(q) for q in wire["fresh"]] for wire in data["wires"]}
    return_names = tuple(map(str, data["returns"][0]))
    output = [q for name in return_names for q in wire_map[name]]
    inputs = [q for wire in data["wires"] if wire["kind"] == "input" for q in wire_map[wire["name"]]]
    loans = [q for wire in data["wires"] if wire["kind"] == "loan" for q in wire_map[wire["name"]]]
    system = sorted(inputs + loans)
    if sorted(output + loans) != system or len(set(output + loans)) != len(system):
        raise ValueError(f"{source_name}: expected-map checker requires every permanent wire returned or retained as a loan")
    if len(output) + len(loans) != len(system):
        raise ValueError(f"{source_name}: output and loan widths do not cover the input space")
    dimension = 2 ** len(system)
    choi = np.zeros((dimension * dimension,), dtype=complex)
    for label in range(dimension):
        bits = {q: (label >> (len(system) - i - 1)) & 1 for i, q in enumerate(system)}
        if source_name == "mcx-dirty-x.s":
            controls = [q for wire in data["wires"] if wire["name"] in {"q1", "q2", "q3"} for q in wire_map[wire["name"]]]
            targets = wire_map["q"]
            if len(controls) != 3 or len(targets) != 1 or len(loans) != 1:
                raise ValueError("mcx-dirty-x expected-map layout is unsupported")
            if all(bits[q] for q in controls):
                bits[targets[0]] ^= 1
        outbits = [bits[q] for q in output + loans]
        refbits = [(label >> (len(system) - i - 1)) & 1 for i in range(len(system))]
        index = 0
        for bit in outbits + refbits:
            index = (index << 1) | bit
        choi[index] = 1 / math.sqrt(dimension)
    base = np.outer(choi, choi.conj())
    row_weights = 0.25 if source_name == "measured-and-twice.s" else 1.0
    return {record_key(record): base * row_weights for record in all_records(data)}


def run_command(executable, command, source):
    result = subprocess.run(
        [executable, command, str(source)], capture_output=True, check=True, text=True
    )
    return result.stdout


def check_file(executable, source):
    allocation, fresh_qasm, reuse_qasm = load_case(executable, source)
    permanent = lambda field: {
        wire["name"]: tuple(map(int, wire[field]))
        for wire in allocation["wires"] if wire["kind"] in {"input", "loan"}
    }
    if permanent("fresh") != permanent("reuse"):
        raise ValueError("fresh and reuse layouts change an input or loan wire mapping")
    fresh, fresh_gates, fresh_lifts, fresh_reads = channels(fresh_qasm, allocation, "fresh")
    reuse, reuse_gates, reuse_lifts, reuse_reads = channels(reuse_qasm, allocation, "reuse")
    ok, deviation, reason = compare_channels(fresh, reuse)
    expected = expected_channel(allocation, os.path.basename(str(source)))
    expected_deviation = None
    if expected is not None:
        expected_ok, expected_deviation, expected_reason = compare_channels(fresh, expected)
        if not expected_ok:
            ok = False
            reason = f"known-map mismatch: {expected_reason or 'density differs'}"
    return {
        "program": os.path.basename(str(source)), "records": len(fresh),
        "freshQubits": int(allocation["freshQubits"]),
        "reuseQubits": int(allocation["reuseQubits"]),
        "freshStaticGateCalls": fresh_gates, "reuseStaticGateCalls": reuse_gates,
        "liftMeasurements": fresh_lifts, "resultMeasurements": fresh_reads,
        "maxDensityDeviation": deviation, "expectedMapDeviation": expected_deviation,
        "choiRecordWeights": [{"record": list(record), "fresh": float(np.trace(fresh[record]).real),
                               "reuse": float(np.trace(reuse[record]).real)} for record in fresh],
        "ok": ok, "reason": reason,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dqt", required=True, help="path to the dqt executable")
    parser.add_argument("--programs", required=True, help="directory of .s examples")
    args = parser.parse_args(argv)
    if not os.path.isdir(args.programs):
        parser.error(f"program directory does not exist: {args.programs}")
    available = set(os.listdir(args.programs))
    missing = set(ADMITTED_PROGRAMS) - available
    if missing:
        parser.error("missing demonstration programs: " + ", ".join(sorted(missing)))
    sources = [os.path.join(args.programs, name) for name in ADMITTED_PROGRAMS]
    results = []
    errors = []
    for source in sources:
        try:
            results.append(check_file(args.dqt, source))
        except (ValueError, KeyError, TypeError, json.JSONDecodeError, subprocess.CalledProcessError) as exc:
            errors.append({"program": os.path.basename(source), "error": str(exc)})
    print(json.dumps({"results": results, "errors": errors}, indent=2))
    return 1 if errors or any(not row["ok"] for row in results) else 0


if __name__ == "__main__":
    sys.exit(main())
