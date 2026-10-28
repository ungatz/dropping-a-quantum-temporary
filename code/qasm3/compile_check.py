"""compile_check.py -- numeric verification of Drop.Lang.Compile's OpenQASM 3
output.

For every <name>.qasm in out-typed/, parsed by the reference `openqasm3`
package (as the retired s_to_qasm3.py did), this file:

  * builds a small statevector simulator over the parsed AST -- `engine.py`
    cannot execute `ctrl(n)@`/`negctrl`, the `U(theta,phi,lambda)` gate, or
    classical `if`/`else` feed-forward, so all three are implemented here
    (see 'apply_modified', 'gate_matrix' and 'run_stmts' below);
  * runs the circuit on every computational-basis input of the visible
    registers, plus the all-ones probe (matching Drop.Lang.Interp.probesFor,
    which <name>.leaves.json's probes were built from), seeding a dirty
    (non-basis) loan's qubits directly at its declared psi since the
    circuit itself carries no preparation gate for it;
  * follows EVERY measurement branch deterministically (no sampling: each
    branch keeps its exact, unnormalised sub-amplitude, mirroring
    Drop.Lang.Machine's 'step' on a 'CLift');
  * matches each reached (probe, branch) pair to the leaf in
    <name>.leaves.json whose 'record' translates (via 'liftInfo') to the
    same raw classical bits, and compares the circuit's final statevector
    to that leaf's 'expectedAmp' -- Drop.Lang.Machine's own leaf amplitude
    with the reclaiming gate already applied at every site
    Drop.Lang.Compile found SAFE (Drop.Lang.Compile.Emit.expectedFinalState) --
    entrywise, tolerance 1e-9;
  * checks, on each matched branch, which qubit each 'result' bit read:
    result[k] must read the k-th qubit of the value that leaf returns
    ('retQubits', read off Drop.Lang.Machine's leaf), each bit once and in
    order, with 'result' exactly that wide. The state comparison cannot see
    this, since it sums over the 'result' bits.

Run from this directory:  nice -n 19 python3 compile_check.py
"""
import glob
import json
import math
import os
import sys

import numpy as np
import openqasm3
from openqasm3 import ast as qast

TOL = 1e-9
OUT_DIR = "out-typed"


# ---------------------------------------------------------------------
# Expression evaluation (angles: integer/float literals, 'pi', +-*/, unary -)
# ---------------------------------------------------------------------

def eval_expr(e):
    if isinstance(e, qast.IntegerLiteral):
        return float(e.value)
    if isinstance(e, qast.FloatLiteral):
        return float(e.value)
    if isinstance(e, qast.Identifier):
        if e.name == "pi":
            return math.pi
        raise ValueError(f"unknown identifier in expression: {e.name}")
    if isinstance(e, qast.UnaryExpression):
        v = eval_expr(e.expression)
        if e.op.name == "-":
            return -v
        if e.op.name == "!":
            return not v
        raise ValueError(f"unknown unary operator {e.op}")
    if isinstance(e, qast.BinaryExpression):
        a = eval_expr(e.lhs)
        b = eval_expr(e.rhs)
        op = e.op.name
        if op == "+":
            return a + b
        if op == "-":
            return a - b
        if op == "*":
            return a * b
        if op == "/":
            return a / b
        if op == "==":
            return a == b
        if op == "&&":
            return bool(a) and bool(b)
        if op == "||":
            return bool(a) or bool(b)
        raise ValueError(f"unknown binary operator {op}")
    # The pinned parser records parentheses through the expression tree's grouping.
    raise ValueError(f"cannot evaluate expression {e}")


# ---------------------------------------------------------------------
# Gate matrices
# ---------------------------------------------------------------------

_H = np.array([[1, 1], [1, -1]]) / math.sqrt(2)
_X = np.array([[0, 1], [1, 0]], dtype=complex)
_Z = np.diag([1, -1]).astype(complex)
_S = np.diag([1, 1j])
_T = np.diag([1, np.exp(1j * math.pi / 4)])
_CX = np.array([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]], dtype=complex)
_CCX = np.eye(8, dtype=complex)
_CCX[[6, 7], [6, 7]] = 0
_CCX[6, 7] = _CCX[7, 6] = 1
_SWAP = np.array([[1, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 0], [0, 0, 0, 1]], dtype=complex)
_CZ = np.diag([1, 1, 1, -1]).astype(complex)


def u3(theta, phi, lam):
    # OpenQASM3 built-in U, not the QASM2 U3 convention. This phase matters
    # when the gate has quantum controls.
    # https://openqasm.com/language/gates.html#built-in-gates
    return np.exp(1j * theta / 2) * np.array(
        [
            [math.cos(theta / 2), -np.exp(1j * lam) * math.sin(theta / 2)],
            [np.exp(1j * phi) * math.sin(theta / 2), np.exp(1j * (phi + lam)) * math.cos(theta / 2)],
        ],
        dtype=complex,
    )


def gate_matrix(name, args):
    if name == "h":
        return _H
    if name == "x":
        return _X
    if name == "z":
        return _Z
    if name == "s":
        return _S
    if name == "t":
        return _T
    if name == "cx":
        return _CX
    if name == "ccx":
        return _CCX
    if name == "swap":
        return _SWAP
    if name == "cz":
        return _CZ
    if name == "p":
        theta = eval_expr(args[0])
        return np.diag([1, np.exp(1j * theta)]).astype(complex)
    if name == "cp":
        theta = eval_expr(args[0])
        return np.diag([1, 1, 1, np.exp(1j * theta)]).astype(complex)
    if name == "U":
        theta, phi, lam = (eval_expr(a) for a in args)
        return u3(theta, phi, lam)
    if name == "ry":
        theta = eval_expr(args[0])
        c, s = math.cos(theta / 2), math.sin(theta / 2)
        return np.array([[c, -s], [s, c]], dtype=complex)
    raise ValueError(f"unknown base gate {name}")


# ---------------------------------------------------------------------
# The simulator: a complex ndarray of shape (2,)*nq, axis q = qubit q
# (qubit 0 most significant, matching Drop.Lang.QState's mixed-radix
# convention, first register most significant).
# ---------------------------------------------------------------------

def apply_unitary(state, nq, targets, U):
    """Apply U (2^m x 2^m, first 'targets' entry most significant) to the
    given qubit axes; every other axis is untouched."""
    m = len(targets)
    others = [q for q in range(nq) if q not in targets]
    perm = list(targets) + others
    st = np.transpose(state, perm)
    shape_rest = st.shape[m:]
    st = st.reshape(2 ** m, -1)
    st = U @ st
    st = st.reshape((2,) * m + shape_rest)
    inv_perm = np.argsort(perm)
    return np.transpose(st, inv_perm)


def apply_modified(state, nq, ctrl_qubits, ctrl_vals, targets, U):
    """ctrl(n)@/negctrl@ ... U q_ctrl.., q_target..: apply U to 'targets'
    only in the subspace where every ctrl qubit equals its required value."""
    if not ctrl_qubits:
        return apply_unitary(state, nq, targets, U)
    idx = [slice(None)] * nq
    for q, v in zip(ctrl_qubits, ctrl_vals):
        idx[q] = v
    idx = tuple(idx)
    remaining = [q for q in range(nq) if q not in ctrl_qubits]
    rel_targets = [remaining.index(q) for q in targets]
    sub = state[idx]
    sub2 = apply_unitary(sub, len(remaining), rel_targets, U)
    state = state.copy()
    state[idx] = sub2
    return state


def qubit_index(id_or_indexed):
    """An IndexedIdentifier q[k] -> k; a plain Identifier (a gate-definition
    formal, resolved by the caller's substitution map) is handled there."""
    return int(id_or_indexed.indices[0][0].value)


def resolve_qubit(qarg, subst):
    """A gate-call qubit argument: either q[k] (subst is irrelevant) or a
    bare formal name inside a custom gate's body (looked up in 'subst')."""
    if isinstance(qarg, qast.IndexedIdentifier):
        return qubit_index(qarg)
    if isinstance(qarg, qast.Identifier):
        return subst[qarg.name]
    raise ValueError(f"cannot resolve qubit argument {qarg}")


def resolve_bit_target(target, creg_sizes):
    """c[k] or result[k] -> (regname, k), refusing a register never
    declared and an index past its declared width."""
    if isinstance(target, qast.IndexedIdentifier):
        reg, k = target.name.name, int(target.indices[0][0].value)
        if reg not in creg_sizes:
            raise ValueError(f"bit register {reg} is not declared")
        if not 0 <= k < creg_sizes[reg]:
            raise ValueError(f"bit {reg}[{k}] is past the declared width {creg_sizes[reg]}")
        return reg, k
    raise ValueError(f"cannot resolve classical target {target}")


def eval_condition(cond, bits):
    if isinstance(cond, qast.BooleanLiteral):
        return cond.value
    if isinstance(cond, qast.BinaryExpression) and cond.op.name == "==":
        lhs = cond.lhs
        if isinstance(lhs, qast.IndexExpression):
            reg = lhs.collection.name
            k = int(lhs.index[0].value)
            v = int(eval_expr(cond.rhs))
            # The emitter measures each lift's bit before any `if` reads it;
            # a bit no measurement has written is refused, not read as 0.
            if (reg, k) not in bits:
                raise ValueError(f"the condition reads {reg}[{k}], which no measurement has written")
            return bits[(reg, k)] == v
        raise ValueError(f"unsupported condition lhs {lhs}")
    if isinstance(cond, qast.UnaryExpression) and cond.op.name == "!":
        return not eval_condition(cond.expression, bits)
    if isinstance(cond, qast.BinaryExpression) and cond.op.name in ("&&", "||"):
        a = eval_condition(cond.lhs, bits)
        b = eval_condition(cond.rhs, bits)
        return (a and b) if cond.op.name == "&&" else (a or b)
    raise ValueError(f"unsupported condition {cond}")


class Program:
    def __init__(self, ast_prog):
        self.nq = 0
        self.creg_sizes = {}
        self.custom_gates = {}
        self.body = []
        for st in ast_prog.statements:
            if isinstance(st, qast.QubitDeclaration):
                self.nq = int(eval_expr(st.size))
                if self.nq <= 0:
                    raise ValueError("quantum register width must be positive")
            elif isinstance(st, qast.ClassicalDeclaration) and isinstance(st.type, qast.BitType):
                size = int(eval_expr(st.type.size)) if st.type.size is not None else 1
                self.creg_sizes[st.identifier.name] = size
            elif isinstance(st, qast.QuantumGateDefinition):
                self.custom_gates[st.name.name] = st
            elif isinstance(st, qast.Include):
                pass
            else:
                self.body.append(st)

    def run_gate_call(self, st, state, subst=None):
        subst = subst or {}
        qubits = [resolve_qubit(q, subst) for q in st.qubits]
        name = st.name.name
        if name in self.custom_gates and not st.modifiers:
            defn = self.custom_gates[name]
            formals = [q.name for q in defn.qubits]
            inner_subst = dict(zip(formals, qubits))
            for inner in defn.body:
                state = self.run_gate_call(inner, state, inner_subst)
            return state
        n_ctrl = len(st.modifiers)
        ctrl_qubits = qubits[:n_ctrl]
        ctrl_vals = [0 if m.modifier.name == "negctrl" else 1 for m in st.modifiers]
        targets = qubits[n_ctrl:]
        U = gate_matrix(name, st.arguments)
        return apply_modified(state, self.nq, ctrl_qubits, ctrl_vals, targets, U)

    def run_stmts(self, stmts, state, bits):
        """Returns a list of (final_state, final_bits), branching at every
        measurement, both branches kept unnormalised (Drop.Lang.Machine's own
        convention: a drop-through-a-branch amplitude is not renormalised)."""
        if not stmts:
            return [(state, bits)]
        st = stmts[0]
        rest = stmts[1:]
        if isinstance(st, qast.QuantumMeasurementStatement):
            q = qubit_index(st.measure.qubit)
            reg, k = resolve_bit_target(st.target, self.creg_sizes)
            idx0 = [slice(None)] * self.nq
            idx0[q] = 1
            s0 = state.copy()
            s0[tuple(idx0)] = 0
            idx1 = [slice(None)] * self.nq
            idx1[q] = 0
            s1 = state.copy()
            s1[tuple(idx1)] = 0
            # Which qubit each bit of the register read, in the order written:
            # the output check below compares result's against the value the
            # machine's leaf returns.
            read = bits.get(("read", reg), ()) + ((k, q),)
            b0 = dict(bits)
            b0[(reg, k)] = 0
            b0[("read", reg)] = read
            b1 = dict(bits)
            b1[(reg, k)] = 1
            b1[("read", reg)] = read
            return self.run_stmts(rest, s0, b0) + self.run_stmts(rest, s1, b1)
        if isinstance(st, qast.BranchingStatement):
            cond = eval_condition(st.condition, bits)
            block = st.if_block if cond else st.else_block
            out = []
            for s2, b2 in self.run_stmts(block, state, bits):
                out += self.run_stmts(rest, s2, b2)
            return out
        if isinstance(st, qast.QuantumGate):
            state2 = self.run_gate_call(st, state)
            return self.run_stmts(rest, state2, bits)
        if isinstance(st, qast.QuantumPhase):
            if st.modifiers or st.qubits:
                raise ValueError("only an unmodified zero-qubit gphase is supported")
            state2 = state * np.exp(1j * eval_expr(st.argument))
            return self.run_stmts(rest, state2, bits)
        if isinstance(st, (qast.QuantumGateDefinition, qast.QubitDeclaration, qast.ClassicalDeclaration, qast.Include)):
            return self.run_stmts(rest, state, bits)
        raise ValueError(f"unsupported top-level statement {type(st).__name__}")


# ---------------------------------------------------------------------
# Building the initial physical state for one probe.
# ---------------------------------------------------------------------

def basis_index_of(psi, tol=1e-6):
    idx = [i for i, z in enumerate(psi) if abs(z) > tol]
    if len(idx) == 1 and abs(abs(psi[idx[0]]) - 1) < tol:
        return idx[0]
    return None


def build_initial(nq, vis_qubits_all, vis_amp, dirty_list):
    covered = set(vis_qubits_all)
    # a program whose inputs are all loans has no visible register (the
    # loan-return fixtures): then there is no visible segment
    segments = [(sorted(vis_qubits_all), np.array(vis_amp, dtype=complex))] if vis_qubits_all else []
    for qs, psi in dirty_list:
        segments.append((sorted(qs), np.array(psi, dtype=complex)))
        covered |= set(qs)
    for q in range(nq):
        if q not in covered:
            segments.append(([q], np.array([1.0, 0.0], dtype=complex)))
    segments.sort(key=lambda s: s[0][0])
    vec = np.array([1.0 + 0j])
    for _, amp in segments:
        vec = np.kron(vec, amp)
    return vec.reshape((2,) * nq)


# ---------------------------------------------------------------------
# Per-program check
# ---------------------------------------------------------------------

def global_phase_deviation(got, expected):
    """Max entrywise deviation after fitting a single global phase (the
    'diff' gate's own header comment: the h;x;cz;x;h decomposition of
    Grover's 2|s><s| - I is that gate only up to the global phase -1, a
    standard, physically unobservable, per-leaf ambiguity -- the retired s_to_qasm3.py
    ported the same decomposition with the same comment). A structural bug
    would still show up: fitting one scalar cannot repair the RELATIVE
    phase or magnitude between two different entries."""
    if expected.size == 0:
        return 0.0
    i = int(np.argmax(np.abs(expected)))
    if abs(expected[i]) < 1e-12:
        return float(np.max(np.abs(got - expected)))
    ph = got[i] / expected[i] if abs(got[i]) > 1e-12 else 1.0
    if abs(abs(ph) - 1) > 1e-3:
        # not a phase at all (a magnitude bug) -- report the raw deviation
        return float(np.max(np.abs(got - expected)))
    ph = ph / abs(ph)
    return float(np.max(np.abs(got - ph * expected)))


def check_program(name):
    qasm_path = os.path.join(OUT_DIR, name + ".qasm")
    json_path = os.path.join(OUT_DIR, name + ".leaves.json")
    if not (os.path.exists(qasm_path) and os.path.exists(json_path)):
        return None
    text = open(qasm_path).read()
    ast_prog = openqasm3.parse(text)  # the reference parser; raises on a malformed program
    prog = Program(ast_prog)
    data = json.load(open(json_path))

    vis_dims = data["visDims"]
    dv = 1
    for d in vis_dims:
        dv = dv * int(d)
    vis_qubits_all = [int(q) for entry in data["visQubits"] for q in entry["qubits"]]
    lift_info = {e["name"]: (int(e["bit"]), int(e["survivedValue"])) for e in data["liftInfo"]}
    dirty_list = []
    for e in data["wireAlloc"]:
        psi = [complex(re, im) for re, im in e["psi"]]
        if basis_index_of(psi) is None:
            dirty_list.append(([int(q) for q in e["qubits"]], psi))
    # Block-lift indicator ancillas: physical qubits with
    # no wire in Drop.Lang.Machine's own leaf state at all. The lemma proves
    # each is reclaimed to |0> unconditionally, so marginalise it out after
    # checking that is actually so -- never silently.
    ancilla_qubits = sorted({int(q) for q in data.get("liftAncilla", [])}, reverse=True)

    leaves_compared = 0
    outputs_checked = 0
    max_dev = 0.0
    mismatches = []

    for probe in data["probes"]:
        p = int(probe["probe"])
        if p < dv:
            vis_amp = [1.0 if i == p else 0.0 for i in range(dv)]
        else:
            vis_amp = [1.0] * dv
        state0 = build_initial(prog.nq, vis_qubits_all, vis_amp, dirty_list)
        branches = prog.run_stmts(prog.body, state0, {})

        for leaf in probe["leaves"]:
            # translate the leaf's (paramName, 1=survived) record into raw
            # (creg, bit) -> qasm-measured-value pairs
            want = {}
            for pname, survived in leaf["record"]:
                if pname not in lift_info:
                    continue
                bit_idx, sv = lift_info[pname]
                want[("c", bit_idx)] = sv if int(survived) == 1 else 1 - sv
            # 'result[i] = measure q[..]' (Drop.Lang.Compile.Emit.outputMeasureLines)
            # re-measures a qubit an earlier 'c[k] = measure' may already
            # have collapsed (or one no lift ever touched), splitting each
            # true leaf into several branches that agree on every 'c[..]'
            # bit and differ only in the (irrelevant, here) 'result' bits.
            # Summing every branch consistent with 'want' recovers the
            # pre-final-measurement amplitude exactly, since at most one of
            # them is not identically the zero vector.
            match = None
            found = False
            reads = set()
            for st, bits in branches:
                relevant = {k: v for k, v in bits.items() if k[0] == "c"}
                if relevant == want:
                    match = st if not found else match + st
                    found = True
                    reads.add(bits.get(("read", "result"), ()))
            expected = np.array([complex(re, im) for re, im in leaf["expectedAmp"]])
            if not found:
                mismatches.append(f"probe {p}: no branch found for record {leaf['record']} (want {want})")
                continue
            # The output check: on this record, result[k] must read the k-th
            # qubit of the value the machine's leaf returns, each bit once, in
            # order, and result must be exactly that wide. The state
            # comparison below cannot see this: it sums over the result bits.
            ret = [int(q) for q in leaf["retQubits"]]
            want_reads = tuple(enumerate(ret))
            if reads != {want_reads}:
                got_reads = sorted(reads)
                mismatches.append(
                    f"probe {p}, record {leaf['record']}: result reads {got_reads}, "
                    f"the value returned is on qubits {ret}"
                )
            elif prog.creg_sizes.get("result", 0) != len(ret):
                mismatches.append(
                    f"probe {p}, record {leaf['record']}: result has {prog.creg_sizes.get('result', 0)} bits, "
                    f"the value returned has {len(ret)} qubits"
                )
            else:
                outputs_checked += 1
            reduced = match
            for q in ancilla_qubits:
                off = np.take(reduced, 1, axis=q)
                if np.max(np.abs(off)) > TOL:
                    mismatches.append(
                        f"probe {p}, record {leaf['record']}: ancilla qubit {q} not reclaimed to |0> "
                        f"(max amplitude at |1> = {float(np.max(np.abs(off))):.3g})"
                    )
                reduced = np.take(reduced, 0, axis=q)
            got = reduced.reshape(-1)
            if got.shape != expected.shape:
                mismatches.append(
                    f"probe {p}, record {leaf['record']}: shape {got.shape} != expected {expected.shape}"
                )
                continue
            dev = global_phase_deviation(got, expected)
            max_dev = max(max_dev, dev)
            leaves_compared += 1
            if dev > TOL:
                mismatches.append(f"probe {p}, record {leaf['record']}: max deviation {dev:.3g}")

    return leaves_compared, outputs_checked, max_dev, mismatches


def main():
    names = sorted(
        os.path.basename(p)[: -len(".qasm")] for p in glob.glob(os.path.join(OUT_DIR, "*.qasm"))
    )
    total_leaves = 0
    total_outputs = 0
    total_fail = 0
    print(f"{len(names)} emitted program(s) in {OUT_DIR}/")
    if not names:
        sys.exit(f"no .qasm file in {OUT_DIR}/: run cabal test in ../haskell first")
    for name in names:
        result = check_program(name)
        if result is None:
            print(f"-- {name}: no leaves.json  [MISSING]")
            total_fail += 1
            continue
        leaves_compared, outputs_checked, max_dev, mismatches = result
        total_leaves += leaves_compared
        total_outputs += outputs_checked
        status = "OK" if not mismatches else "MISMATCH"
        print(f"-- {name}: {leaves_compared} leaves compared, max deviation {max_dev:.3g}, "
              f"result read right on {outputs_checked}  [{status}]")
        for m in mismatches[:20]:
            print(f"     {m}")
            total_fail += 1
        if len(mismatches) > 20:
            print(f"     ... and {len(mismatches) - 20} more")
            total_fail += len(mismatches) - 20
    print(f"\non {total_outputs} leaves, result[k] reads the k-th qubit of the value the leaf returns")
    print(f"{total_leaves} leaves compared across {len(names)} programs, {total_fail} mismatch(es)")
    if total_fail:
        sys.exit(1)


if __name__ == "__main__":
    main()
