#!/usr/bin/env python3.11
"""Check numerical gate emission against independently specified source maps."""
from __future__ import annotations

import argparse
import math
import sys
import tempfile
from fractions import Fraction
from pathlib import Path

import numpy as np

QASM_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(QASM_DIR))
import compile_check as sim
import reuse_check as rc

TOL = 1e-9
FIXTURES = {
    "controlled_return_phase.s": """prog controlled_return_phase (v : [2]) : [2] * [2] {
  new a : [2] @ |0>; new b : [2] @ |0>;
  X b; H a;
  drop (a, b);
  new t : [2] @ |0>;
  return (v, t)
}
""",
    "near_hadamard.s": """prog near_hadamard (v : [2]) : [2] * [2] {
  new t : [2] @ |0>;
  mat t { 35/37, -12/37 ; 12/37, 35/37 };
  mat t { 160832/179057, -78705/179057 ; 78705/179057, 160832/179057 };
  drop t;
  new s : [2] @ |0>;
  return (v, s)
}
""",
    "small_rotation.s": """prog small_rotation (v : [2]) : [2] {
  mat v { 4000008000003/4000008000005, -4000004/4000008000005 ;
          4000004/4000008000005, 4000008000003/4000008000005 };
  return v
}
""",
    "identity.s": """prog identity (v : [2]) : [2] {
  mat v { 1, 0 ; 0, 1 };
  return v
}
""",
    "exact_basis.s": """prog exact_basis (v : [2]) : [2] * [2] {
  new t : [2] @ |1>;
  drop t;
  new s : [2] @ |0>;
  return (v, s)
}
""",
    "near_basis.s": """gate Ra : [2] = mat {
  47999991999999/80000008000001, -64000016000000/80000008000001;
  64000016000000/80000008000001, 47999991999999/80000008000001 };
gate Rb : [2] = mat { 3/5, 4/5; -4/5, 3/5 };
prog near_basis (v : [2]) : [2] * [2] {
  new t : [2] @ |0>; new w : [2] @ |0>;
  Ra t; Rb t; drop (t, w);
  new u : [2] @ |0>; return (v, u)
}
""",
    "near_permutation.s": """prog near_permutation (v : [2], loan a : [2], loan b : [2]) : [2] {
  mat a { 4000008000003/4000008000005, -4000004/4000008000005;
          4000004/4000008000005, 4000008000003/4000008000005 };
  drop (a, b); return v
}
""",
    "permutation.s": """prog permutation (v : [2], loan a : [2], loan b : [2]) : [2] {
  Swap a b; drop (a, b); return v
}
""",
    "thin_four_support.s": """prog thin_four_support (v:[2]):[2]*[2] {
 new t:[2] @ |0>; new w:[2] @ |0>;
 mat t { 3/5, -4/5; 4/5, 3/5 };
 mat w { 399999999999999999999999999/400000000000000000000000001, -40000000000000/400000000000000000000000001; 40000000000000/400000000000000000000000001, 399999999999999999999999999/400000000000000000000000001 };
 drop (t,w);
 new s:[2] @ |0>; return (v,s)
}
""",
    "three_lifetimes.s": """prog three_lifetimes (v : [2]) : [2] {
  new t0 : [2] @ |1>; H t0; CX v t0; drop t0;
  new t1 : [2] @ |1>; H t1; CX v t1; drop t1;
  new t2 : [2] @ |1>; H t2; CX v t2; drop t2;
  return v
}
""",
}


def rational_rotation_fixture(exponent, flipped=False):
    s = Fraction(1, 10 ** exponent)
    a, b = (1 - s*s)/(1 + s*s), 2*s/(1 + s*s)
    if flipped:
        a, b = b, a
    return f"""prog numeric_basis (v : [2]) : [2] {{
  new t : [2] @ |0>;
  mat t {{ {a}, {-b}; {b}, {a} }};
  drop t; return v
}}
"""


def galois_fixture(block=False):
    # Exact Q(sqrt(2)) arithmetic, independent of the compiler's ray conversion.
    x = Fraction(3232233047033631, 5000000000000000)
    def mul(z, w):
        a, b = z; c, d = w
        return a*c + 2*b*d, a*d + b*c
    def div(z, w):
        c, d = w
        den = c*c - 2*d*d
        return mul(z, (c/den, -d/den))
    def scalar(z):
        a, b = z
        return f"{a}+{2*b}*1/rt2"
    den = (Fraction(9, 8) + x*x, -x/2)
    a = div((Fraction(7, 8) - x*x, x/2), den)
    b = div((2*x, Fraction(-1, 2)), den)
    minus_b = tuple(-z for z in b)
    extra = "new u : [2] @ |0>;" if block else ""
    dropped = "(t, u)" if block else "t"
    return f"""prog numeric_galois (v : [2]) : [2] {{
  new t : [2] @ |0>; {extra}
  mat t {{ {scalar(a)}, {scalar(minus_b)}; {scalar(b)}, {scalar(a)} }};
  drop {dropped}; return v
}}
"""


NUMERIC_BASIS_FIXTURES = {
    "basis_tiny_100.s": rational_rotation_fixture(100),
    "basis_tiny_163.s": rational_rotation_fixture(163),
    "basis_flipped_160.s": rational_rotation_fixture(160, flipped=True),
    "basis_galois.s": galois_fixture(),
    "basis_galois_block.s": galois_fixture(block=True),
}
FIXTURES.update(NUMERIC_BASIS_FIXTURES)

# The unrelated temporary scales the exact extracted loan factor. The oracle
# remains identity on the input and unknown, reference-entangled loan.
LOAN_SCALE_FIXTURES = {
    f"loan_tiny_{k}.s": rational_rotation_fixture(k, flipped=True)
        .replace("numeric_basis (v : [2])", "loan_tiny (v : [2], loan a : [2])")
        .replace("drop t; return v", "H a; drop a; drop t; return v")
    for k in (100, 163, 200, 400)
}
LOAN_SCALE_FIXTURES["loan_phase_orientation.s"] = """prog loan_phase (v : [2], loan a : [2]) : [2] {
  mat a { 1, 0; 0, i }; H a; drop a; return v
}
"""
FIXTURES.update(LOAN_SCALE_FIXTURES)


def expected_channel(data, mode, fixture):
    field = "fresh" if mode == "fresh" else "reuse"
    wires = {w["name"]: [int(q) for q in w[field]] for w in data["wires"]}
    system = sorted(q for w in data["wires"] if w["kind"] in {"input", "loan"}
                    for q in wires[w["name"]])
    returned = [q for name in map(str, data["returns"][0]) for q in wires[name]]
    loans = [q for w in data["wires"] if w["kind"] == "loan" for q in wires[w["name"]]]
    output = returned + loans
    d = 2 ** len(system)
    if fixture == "three_lifetimes.s":
        # Each |-> kickback contributes Z; three lifetimes therefore give Z.
        k = np.diag([1, -1]).astype(complex)
    elif fixture == "small_rotation.s":
        den = 4000008000005
        p, q = 4000008000003 / den, 4000004 / den
        k = np.array([[p, -q], [q, p]], dtype=complex)
    else:
        # Dropped loans, including near_permutation, are handed back by
        # the inserted return. Their expected map is identity, not the
        # source prefix's rotation before that return.
        k = np.zeros((2 ** len(output), d), dtype=complex)
        for i in range(d):
            input_bits = {q: (i >> (len(system) - j - 1)) & 1 for j, q in enumerate(system)}
            out = 0
            for q in output:
                out = (out << 1) | input_bits.get(q, 0)
            k[out, i] = 1
    vector = k.reshape(-1) / math.sqrt(d)
    return {rc.record_key([]): np.outer(vector, vector.conj())}


def pooled_wire_leak(qasm, data, mode, wire):
    program = sim.Program(sim.openqasm3.parse(qasm))
    rc.result_measurements(program)
    width, wire_map, inputs, loans, temp_bits = rc.validate_allocation(data, program, mode)
    nref = len(inputs) + len(loans)
    program.nq = width + nref
    states = program.run_stmts(program.body, rc.initial_state(width, inputs, loans, temp_bits), {})
    return max(float(np.max(np.abs(np.take(state, 1, axis=q))))
               for state, _ in states for q in wire_map[wire])


def output_on_zero(qasm, data, mode, wire):
    program = sim.Program(sim.openqasm3.parse(qasm))
    rc.result_measurements(program)
    width, wire_map, inputs, loans, temp_bits = rc.validate_allocation(data, program, mode)
    if width != 1 or wire_map[wire] != [0] or inputs != [0] or loans:
        raise ValueError(f"{wire}: expected a one-qubit input-only fixture")
    program.nq = width
    initial = np.array([1, 0], dtype=complex).reshape((2,))
    branches = program.run_stmts(program.body, initial, {})
    if len(branches) != 1:
        raise ValueError(f"{wire}: expected one unmeasured branch")
    state, _ = branches[0]
    return np.array([state[0], state[1]], dtype=complex)


def demand_close(label, got, expected):
    deviation = float(np.max(np.abs(got - expected)))
    print(f"{label}: max deviation {deviation:.3g}")
    if not math.isfinite(deviation) or deviation > TOL:
        raise AssertionError(f"{label}: deviation {deviation:.3g} > {TOL:g}")


def check_case(executable, source):
    data, fresh_qasm, reuse_qasm = rc.load_case(executable, source)
    if any(token in text for text in (fresh_qasm, reuse_qasm)
           for token in ("NaN", "Infinity")):
        raise AssertionError("non-finite emitted gate parameter")
    fresh = rc.channels(fresh_qasm, data, "fresh")
    reuse = rc.channels(reuse_qasm, data, "reuse")
    expected_fresh = expected_channel(data, "fresh", source.name)
    expected_reuse = expected_channel(data, "reuse", source.name)
    demand_close(source.name + " fresh Choi", fresh[0][rc.record_key([])],
                 expected_fresh[rc.record_key([])])
    demand_close(source.name + " reuse Choi", reuse[0][rc.record_key([])],
                 expected_reuse[rc.record_key([])])
    ok, dev, why = rc.compare_channels(fresh[0], reuse[0])
    print(f"{source.name} fresh/reuse Choi: max deviation {dev:.3g}")
    if not ok:
        raise AssertionError(why or f"fresh/reuse deviation {dev:.3g}")
    if source.name in {"near_hadamard.s", "near_basis.s"}:
        for mode, qasm in (("fresh", fresh_qasm), ("reuse", reuse_qasm)):
            leak = pooled_wire_leak(qasm, data, mode, "t")
            print(f"{source.name} {mode} pooled t |1> amplitude: {leak:.3g}")
            if leak > TOL:
                raise AssertionError(f"{mode} pooled t residual {leak:.3g} > {TOL:g}")
    if source.name == "controlled_return_phase.s":
        # The fixed state |+1> needs a three-support Householder axis.
        # Wrong controlled-U phases leave scratch dirty; reuse then exposes
        # that error in returned t. Check all physical scratch as well.
        for mode, qasm in (("fresh", fresh_qasm), ("reuse", reuse_qasm)):
            for wire in ("a", "b", "t"):
                leak = pooled_wire_leak(qasm, data, mode, wire)
                print(f"{source.name} {mode} {wire} |1> amplitude: {leak:.3g}")
                if not math.isfinite(leak) or leak > TOL:
                    raise AssertionError("controlled return did not restore scratch")
    if source.name in NUMERIC_BASIS_FIXTURES:
        for mode, qasm in (("fresh", fresh_qasm), ("reuse", reuse_qasm)):
            leak = pooled_wire_leak(qasm, data, mode, "t")
            print(f"{source.name} {mode} scratch |1> amplitude: {leak:.3g}")
            if not math.isfinite(leak) or leak > TOL:
                raise AssertionError("scratch was not restored to zero")
    if source.name in {"identity.s", "permutation.s", "near_permutation.s"}:
        if any("not emitted" in text for text in (fresh_qasm, reuse_qasm)):
            raise AssertionError("these exact safe loan factors must have an emitted return")
    if source.name == "exact_basis.s":
        leak = pooled_wire_leak(reuse_qasm, data, "reuse", "t")
        print(f"exact_basis reuse pooled t |1> amplitude: {leak:.3g}")
        if leak > TOL:
            raise AssertionError(f"reuse pooled t residual {leak:.3g} > {TOL:g}")
    if source.name == "thin_four_support.s":
        import allocation_check
        if (data["freshQubits"] != 4 or data["reuseQubits"] != 3
                or len(data["sites"]) != 1 or not data["sites"][0]["pooled"]):
            raise AssertionError("the thin four-support block was not reclaimed and reused")
        if allocation_check.check_pools(reuse_qasm, data) != 1:
            raise AssertionError("expected one clean two-wire block release")
        for mode, qasm in (("fresh", fresh_qasm), ("reuse", reuse_qasm)):
            for wire in ("t", "w", "s"):
                leak = pooled_wire_leak(qasm, data, mode, wire)
                print(f"{source.name} {mode} {wire} |1> amplitude: {leak:.3g}")
                if not math.isfinite(leak) or leak > TOL:
                    raise AssertionError("thin four-support reclaim exceeded numerical tolerance")
        print("thin_four_support: 4 to 3 qubits, one clean two-wire block release")
    if source.name == "three_lifetimes.s":
        import allocation_check
        temps = [w for w in data["wires"] if w["kind"] == "temporary"]
        if (data["freshQubits"] != 4 or data["reuseQubits"] != 2
                or len(temps) != 3
                or any(w["reuse"] != temps[0]["reuse"] for w in temps)
                or not all(s["pooled"] for s in data["sites"])):
            raise AssertionError("three nonzero allocations did not reuse one physical wire")
        checkpoints = allocation_check.check_pools(reuse_qasm, data)
        if checkpoints != 3:
            raise AssertionError(f"expected three clean release checkpoints, got {checkpoints}")
        print("three_lifetimes: 4 to 2 qubits, three clean release checkpoints")
    if source.name in {"small_rotation.s", "identity.s"}:
        if source.name == "small_rotation.s":
            den = 4000008000005
            expected = np.array([4000008000003 / den, 4000004 / den], dtype=complex)
        else:
            expected = np.array([1, 0], dtype=complex)
        for mode, qasm in (("fresh", fresh_qasm), ("reuse", reuse_qasm)):
            actual = output_on_zero(qasm, data, mode, "v")
            demand_close(f"{source.name} {mode} output density on |0>",
                         np.outer(actual, actual.conj()),
                         np.outer(expected, expected.conj()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dqt", required=True, help="path to built dqt executable")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="qasm-emission-regression-") as tmp:
        directory = Path(tmp)
        sources = []
        for name, source in FIXTURES.items():
            path = directory / name
            path.write_text(source)
            sources.append(path)
        for source in sources:
            check_case(args.dqt, source)


if __name__ == "__main__":
    main()
