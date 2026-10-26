# Safe to Drop: an Exact Criterion for Quantum Temporaries

When can a quantum compiler restore a temporary register by acting on that
register alone, without changing the rest of the computation?

- [`abstract/abstract.pdf`](abstract/abstract.pdf) is the extended abstract;
  its LaTeX and figure sources are in [`abstract/`](abstract/).
- [`code/haskell/`](code/haskell/) contains the typed language, safety checkers,
  OpenQASM 3 compiler, examples and tests.
- [`code/qasm3/`](code/qasm3/) compares the emitted circuits with the
  interpreter's results using numerical simulation.
- [`narrative/`](narrative/) contains the earlier full-paper draft.

## Build and run

```sh
(cd abstract && make abstract)
(cd code/haskell && cabal test all)
(cd code/haskell && cabal run dqt -- run programs/mcx-dirty.s)
```

The [Haskell README](code/haskell/README.md) lists the commands, in the shell
and in the REPL. The [OpenQASM README](code/qasm3/README.md) gives the Python
dependencies and the circuit checks. Verdict calculations are
exact; emitted gate parameters and circuit comparisons use numerical arithmetic.

MIT; see [`LICENSE`](LICENSE).
