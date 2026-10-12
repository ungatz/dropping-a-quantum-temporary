# DQT checker and compiler

This package contains a typed language for quantum programs with temporary
registers. It checks when a register may be dropped, runs the programs, and
compiles a supported subset to OpenQASM 3.

## Run it

From this directory:

```sh
cabal test all
cabal run dqt -- list
cabal run dqt -- typecheck programs/dj.s
cabal run dqt -- run programs/mcx-dirty.s
cabal run dqt -- compile programs/dj.s
```

`list` shows the theory examples. `typecheck`, `run`, and `compile` accept a
`.s` file. `compile` writes OpenQASM 3 to standard output. `cabal test all`
runs the four test suites. The compiler suite writes `.qasm` circuits and leaf
data to the sibling `../qasm3/out-typed/` directory.

The language syntax and examples are in [`programs/SYNTAX.md`](programs/SYNTAX.md)
and [`programs/`](programs/).

## What the checks establish

The theory route constructs site maps and checks Kraus-block proportionality
with exact linear algebra over algebraic numbers. The language route probes
the typed execution at each drop site. The bridge compares those verdicts;
the routes use distinct procedures but share arithmetic through the bridge.
The four Haskell suites check the theory examples, language semantics, compiler,
and refusal of malformed typed programs.

The OpenQASM checker in `../qasm3/` parses emitted circuits with the
`openqasm3` reference parser, simulates every tested input and measurement
branch, and compares the result numerically with the Haskell leaf data. It also
checks that each output bit reads the corresponding returned qubit. This is a
numerical comparison of generated circuits; it is not hardware execution or a
physical qubit-reuse allocator.

## Compiler assumptions and diagnostics

The emitted circuit assumes fresh qubits start in `|0⟩`; visible input qubits
carry the caller's input state. A non-basis `new` state is reported as
`preparation of psi assumed (not emitted)`: the compiler does not synthesize
that preparation. A safe site outside its lowering support is reported as
`not emitted`. An unsafe drop is marked `dropped unsafe`. A successful process
exit alone does not certify that every dropped register was returned.
Reclaiming ordinary inputs is unsupported: the checker can find a fixed final
state, but those inputs have no declared state to restore.

The verdict and certificate calculations use exact arithmetic. OpenQASM gate
angles can require decimal approximations, and the separate circuit comparison
uses a numerical tolerance.
