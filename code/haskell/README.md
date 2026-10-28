# dqt

The language of the paper in Haskell: its type checker, its machine, the drop checker and the
compiler to OpenQASM 3. Two checkers decide each drop by different algorithms, one on state
vectors (`src/Drop/Lang/`) and one on matrices (`src/Drop/Theory/`); `src/Drop/Bridge.hs`
compares them. The drop checkers use exact arithmetic; the compiler computes return-gate
parameters numerically. The library needs only `base` and `containers`.
The typed checker and command line refuse state dimensions beyond the machine index range.

```
cabal test                                 # the five test suites
cabal run dqt                              # the list of commands
cabal run dqt -- run programs/temp-and.s   # run one program and judge its drops
cabal run dqt -- run programs/record-parity.s # two lifts, four record verdicts
cabal run dqt -- compile programs/dj.s     # compile one program to OpenQASM 3
cabal run dqt -- all                       # every report
python3 check-examples.py                  # run the examples in the comments
```

In the REPL (`cabal repl lib:dqt`):

```haskell
import Drop.Lang.Report.Run
import Drop.Lang.Report.Trace
import Drop.Lang.Report.Explain
runFile "programs/temp-and.s"              -- the verdict at each drop, per record
typecheckFile "programs/dj.s"              -- the type
compileFile "programs/a-then-u.s"          -- OpenQASM 3
traceFile "programs/temp-and.s" Nothing    -- the run, frame by frame
passFile "programs/rus.s"                  -- the static pass, stage by stage
```

`:m *Drop.Lang.Criterion` opens any module; most definitions are followed by
`-- >>>` examples that can be pasted as they are.

```
src/Drop/Lang/      the language: syntax, types, machine, drop checker, parser, compiler
src/Drop/Theory/    the matrix checker
src/Drop/Bridge.hs  the comparison of the two
app/Main.hs         the dqt command
test/               the test suites
programs/           the example programs; the grammar is programs/SYNTAX.md
examples/paper/     the other programs the paper prints, and one non-basis allocation
EMITTER.md          how the compiler emits a drop
```
