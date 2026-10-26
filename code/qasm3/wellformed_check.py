"""wellformed_check.py -- the two checkers here refuse an ill-formed program by name.

`s_bench.py` reads `.s` text with its own parser and `compile_check.py` reads
OpenQASM 3 with the reference one, and neither went through the Haskell
statics.  Each program below breaks one rule the Haskell side enforces; each
must raise a ValueError whose message names it.  Unchecked, `s_bench` would
call a drop SAFE with a gate after it, and `compile_check` would simulate a
branch on a bit nothing had measured.

Run from this directory:  nice -n 19 python3 wellformed_check.py
(s_bench needs numpy; compile_check needs openqasm3 as well.)
"""
import sys

import s_bench

HEAD = "prog f (v : [2]) : [2] {\n"
TAIL = "  return v\n}\n"

S_CASES = [
    ("a gate after the drop", "has been dropped",
     "  new t : [2] @ (1, 0);\n  H t;\n  drop t;\n  CX t v;\n"),
    ("a register dropped twice", "has been dropped",
     "  new t : [2] @ |0>;\n  drop t;\n  drop t;\n"),
    ("a lift on a dropped register", "has been dropped",
     "  new t : [2] @ |0>;\n  H t;\n  drop t;\n  p = lift[{1}] t;\n  new s : [2] @ |0>;\n  drop s;\n"),
    ("a gate before the allocation", "no register t",
     "  X t;\n  new t : [2] @ |0>;\n  drop t;\n"),
    ("a lift block that is every level", "nonempty proper",
     "  new t : [2] @ |0>;\n  H t;\n  p = lift[{0, 1}] t;\n  drop t;\n"),
    ("a non-unitary diag", "not unitary",
     "  new t : [2] @ |0>;\n  diag t (2, 1);\n  drop t;\n"),
    ("a state that is not a unit vector", "unit state",
     "  new t : [2] @ (1, 1);\n  drop t;\n"),
    ("a state of the wrong length", "needs 2 amplitudes",
     "  new t : [2] @ (1, 0, 0);\n  drop t;\n"),
    ("one register twice in a gate", "named twice",
     "  new t : [2] @ |0>;\n  CX t t;\n  drop t;\n"),
    ("an if on a parameter never lifted", "not lifted",
     "  new t : [2] @ |0>;\n  if q { X t; } else { }\n  drop t;\n"),
]

QASM_CASES = [
    ("an if on a bit never measured", "no measurement has written",
     "OPENQASM 3.0;\nqubit[2] q;\nbit[1] c;\nbit[1] result;\n"
     "if (c[0] == 1) { x q[0]; } else { }\nresult[0] = measure q[0];\n"),
    ("a bit past the declared width", "past the declared width",
     "OPENQASM 3.0;\nqubit[2] q;\nbit[1] c;\nbit[1] result;\n"
     "c[3] = measure q[1];\nresult[0] = measure q[0];\n"),
]


def refuses(name, want, thunk, tally):
    try:
        thunk()
    except ValueError as e:
        if want in str(e):
            print("  PASS ", name); tally[0] += 1
        else:
            print("  FAIL ", name, "-- refused, but said:", e); tally[1] += 1
        return
    print("  FAIL ", name, "-- answered instead of refusing"); tally[1] += 1


def main():
    tally = [0, 0]
    print("s_bench.parse_s and drop_verdicts")
    for name, want, body in S_CASES:
        def run(body=body):
            regs, vis, loans, starts, stmts = s_bench.parse_s(HEAD + body + TAIL)
            for site in s_bench.drop_sites(stmts):
                s_bench.drop_verdicts(regs, vis, loans, starts, stmts, site)
        refuses(name, want, run, tally)
    print("s_bench on a generated statement list")
    refuses("a family that gates its temporary after the drop", "has been dropped",
            lambda: s_bench.drop_verdicts([("v", 2), ("t", 2)], ["v"], [], {},
                                          [("new", "t"), ("drop", "t"), ("gate", ["t", "v"], s_bench.CXg)], "t"),
            tally)
    try:
        import numpy as np
        import openqasm3
        import compile_check
    except ImportError:
        print("compile_check: openqasm3 is not installed here, so its two cases were not run")
    else:
        print("compile_check.Program.run_stmts")
        for name, want, text in QASM_CASES:
            def run(text=text):
                prog = compile_check.Program(openqasm3.parse(text))
                state = np.zeros((2,) * prog.nq, dtype=complex)
                state[(0,) * prog.nq] = 1
                prog.run_stmts(prog.body, state, {})
            refuses(name, want, run, tally)
    print("%d passed, %d failed" % (tally[0], tally[1]))
    sys.exit(1 if tally[1] else 0)


if __name__ == "__main__":
    main()
