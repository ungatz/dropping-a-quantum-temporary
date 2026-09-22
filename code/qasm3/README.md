# qasm3/ — the per-record table as a compiler output

Two Python scripts on one small numerical engine, plus a checker for the
Haskell emitter, beside the Haskell artifact itself:

* `s_bench.py` — reads every `.s` program of `../haskell/programs/` (its own small parser for
  the surface syntax of `programs/SYNTAX.md`: the `prog` header with its `loan` parameters, the
  three gate literals, `lift`, `if` and `drop`) and three generated
  families (an m-controlled X with Barenco's m−2 dirty ancillas, m = 3, 4, 5; Deutsch–Jozsa,
  Grover's mark, Bennett's compute–copy–uncompute, the measured-and-fixed-up AND), computes the
  paper's verdict at every drop site on every reachable record, and prints, per site, what
  three reuse schedules pay: measure-and-reset (one mid-circuit measurement and reset per
  temporary per shot), uncompute (the temporary's gates again), and this paper (nothing per
  shot on a safe site; one exact pass per reachable record, once). Output: `s_bench_table.md`.
  Every corpus verdict agrees with the header of its `.s` file, and a file that does not parse is a hard failure, never a silently missing row. A loan carries no declared state, so it is varied over its own basis like a visible register, and its drop is decided by the block-factor test of the site definition's clause (4) (`loan_verdict`), not by the fixed-ray test a temporary gets; the generated Barenco family declares its dirty ancillas as loans for the same reason. `check_loan_test_is_not_the_ray_test` is the gate: `test/fixtures/cz-loan.s` passes the ray test and fails the block-factor test, and the script asserts UNSAFE there before it writes a table.
* `engine.py` — the machine of the language, numerically (tolerance 1e−8).
  The Haskell package next door is the exact one.
* `compile_check.py` — numeric verification of `Drop.Lang.Compile`'s OpenQASM 3 output, the
  emitter for the typed surface language: for every `<name>.qasm` in
  `out-typed/` (written by `../haskell/test/CompileSpec.hs`, which also writes the matching
  `<name>.leaves.json`), it re-simulates the circuit with the reference `openqasm3` parser,
  follows every measurement branch exactly, and compares the result to
  `Drop.Lang.Machine`'s own leaf amplitude with the reclaiming gate applied, entrywise, tolerance
  1e-9. Run `cabal test` first (it populates `out-typed/`), then, from this directory,
  `nice -n 19 python3 compile_check.py`.

Run `nice -n 19 python3 s_bench.py` from this directory. Requires numpy and, for
`compile_check.py`, the `openqasm3` package.

