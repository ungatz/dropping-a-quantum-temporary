# The affine drop calculus, and its checker

When may a quantum temporary be dropped, and what does deciding it cost? The
package answers that twice, with two implementations that share no code, and
`DQT.Bridge` runs them against each other.

* `src/DQT`, the theory layer: builds the denotation `K : H_m -> H_d (x) H_m`
  as a matrix, forms its Kraus operators, and takes an exact rank.
* `src/S`, the language layer: never builds `K`. It runs a program on
  `dim + 1` test inputs, factors the state at the drop site, and asks whether
  the lines agree.

Arithmetic is exact everywhere. The theory layer works over `Q(w)` with `w` a
primitive eighth root of unity, the language layer over the smallest field
that states each program, up the tower `Q`, `Q[sqrt2]`, `Q(zeta_{2^k})`. A
check walks the sources and fails if any inexact numeric type appears.

## Layout

```
src/DQT.hs             one import that brings the theory layer into scope
src/DQT/Algebra/       the exact field and the matrices
src/DQT/Calculus/      syntax, typing, and the two semantics
src/DQT/Criterion/     the criterion by two routes, its converse, and contexts
src/DQT/Many/          several temporaries: bundling, nesting, the pool
src/DQT/Corpus/        the catalogue, the producer rules, the classical core
src/DQT/Lifted.hs      the lifted calculus, and Lifted/Programs.hs its witnesses
src/DQT/Residual.hs    the runtime check over the lifted calculus
src/DQT/Bridge.hs      the two engines, run against each other

src/S/Lang/            the surface language: syntax, scalars, states, parser, interpreter
src/S/Pass/            the static pass, one module per pass
src/S/Pass.hs          the chain of forms, and the table the pass emits
src/S/Programs/        the corpus, one module per program
src/S/Report/          what the command line prints: run, trace, pass
src/S/Test/            the checks on the parser, the enumeration, and the passes

app/Main.hs    the dqt command line
test/Spec.hs   one named check per statement, plus three gates on the package
programs/      the surface corpus, .s files; SYNTAX.md is the one-page reference
```

The Silq programs of the comparison table and their transcripts are in
`../silq/`, reference material and not part of this build.

## Running it without building anything

Everything runs on `base` alone (the check suite also uses `directory`), so
nothing needs installing:

```
runghc -isrc test/Spec.hs                       # the whole check suite
runghc -isrc app/Main.hs                        # the subcommand list
runghc -isrc app/Main.hs all                    # every report at once
runghc -isrc app/Main.hs run programs/mcx-dirty.s
runghc -isrc app/Main.hs trace programs/dj.s      # the run, one frame per statement
runghc -isrc app/Main.hs pass programs/tilt.s     # the static pass, stage by stage
runghc -isrc app/Main.hs suite                  # the language layer alone
```

The suite runs the language layer first, then the named statements, and exits
non-zero on any failure. Under `runghc` it takes about a quarter of an hour,
most of it in the bounded enumeration; `cabal test` is much faster.

## Running it with cabal

```
cabal build
cabal run dqt -- all
cabal test
```

`cabal.project` names this directory as the only package. The library exposes
every module under `src`; the executable is `dqt`; the check suite is
`dqt-test`.

## Every printed number, and what computes it

Each row names the function that computes the number and the check that pins
it. None is transcribed by hand.

| number | computed by | pinned by |
| --- | --- | --- |
| the criterion accepts twelve of the seventeen catalogue programs | `DQT.Corpus.Producer.safeCount`, `DQT.Corpus.Examples.catalogue` | `the-producer-table-totals-are-the-appendix-row`, `the-verdicts-are-the-expected-ones` |
| R1 (gate classicality) accepts four, and one acceptance is wrong | `DQT.Corpus.Producer.r1Count`, `qfreeUnsoundnessWitnesses` | `the-producer-table-totals-are-the-appendix-row`, `gate-classicality-alone-is-an-unsound-discard-rule` |
| R2 (classicality and no inflow) accepts two, and is sound | `DQT.Corpus.Producer.r2Count`, `producerIsSound` | `the-producer-table-totals-are-the-appendix-row`, `a-producer-discipline-is-sound-and-strictly-incomplete` |
| the classicality gap is an unbounded family, one witness per dimension | `DQT.Corpus.Examples.computeAloneAt` | `gate-classicality-fails-at-every-dimension` |
| the restore-to-allocation rule accepts 4 of the 12; the gap is (12, 8) | `DQT.Many.Release.restorationGap` | `the-restoration-gap-is-eight-of-twelve` |
| the ray each safe program leaves the temporary on: (1,0), (1,1), (1,-1) | `DQT.Criterion.parkedLine`, printed by `DQT.Many.Release.poolReport` | `the-restoration-rule-is-sound-but-not-complete` |
| the runtime table for the witness: refuse on the block {0,1}, accept on {2}; accept on both once the read is deleted | `DQT.Residual.residualCheck`, printed by `explainTable`; `S.Pass`, printed by `dqt pass programs/tilt.s` | `the-residual-table-agrees-with-the-semantic-criterion`, `the-residual-pass-is-exhaustive-and-agrees` |
| the two numbers the read family turns on, 1/2 and 4/9 | `DQT.Criterion.readFamilyMinimaxSquared`, `productReplacementErrorSquared` | `the-read-family-minimax` |
| the C3X borrowed-ancilla lines: (1,0) for the loan on \|0>, (1,1) for the loan on \|+>, refused once the fourth Toffoli is deleted | `S.Report.Run.runText` on `programs/mcx-dirty*.s` | `the-borrowed-ancilla-returns-on-the-loans-own-ray`, `the-borrowed-ancilla-verdict-does-not-depend-on-the-loan`, `deleting-the-restoring-toffoli-is-refused` |
| how many theory statements hold, out of how many | `test/Spec.hs`, last two lines of its output | the suite itself |
| how many checks the language layer runs, in how many groups, over how many algorithms | `S.Suite.suiteCheckCount`, `suiteGroups`, `suiteAlgorithms` | `the-language-suite-passes` |

`restorationGap` is a pair `(accepted, refused by the weaker rule)`: the
second component is the size of the gap, not of the rule.

## The catalogue verdicts, one reason each

`expectedVerdicts` in `test/Spec.hs` is the one table in the package written
by hand rather than computed. The reasons, in one line each:

* `example-A` safe: both reads are no-ops, because the control is at basis state 0.
* `example-B` unsafe: H then one read gives Kraus operators `I/sqrt2` and `X/sqrt2`.
* `example-C` safe: the two reads compose to the identity on the visible register.
* `park`, `in-shape`, `do-nothing` safe: nothing touches the visible register,
  or the program is literally of the separable shape.
* `silq-two-gate` safe: `H H = 1`.
* `tilt-read` unsafe: dimension three gives three independent Kraus operators.
* `dj-constant`, `dj-balanced`, `bv-0`, `bv-1` safe: phase kickback leaves the
  ancilla alone.
* `grover-oracle` safe: compute, mark, uncompute.
* `kickback`, `cz-copy` unsafe: a controlled-Z after a spread entangles.
* `copy-copy` safe: copying twice is the identity.
* `compute-alone` unsafe: one permutation copies the visible register into the
  temporary, and that is the whole leak.

The language layer decides its programs the same way, by probing. Three turn
on a lift:

* `shor.s` (order finding, N = 15, a = 7): unmeasured the residue register is
  unsafe; measured, safe on the block {7} and unsafe on its complement.
* `simon.s` (hidden string 11): unmeasured unsafe; measured, safe on both
  records but on different lines, since f takes only the values 0 and 1.
* `temp-and.s` (Gidney's measurement-based AND uncompute): unmeasured unsafe;
  with H, a measurement and the CZ correction, safe on both records, and the
  correction is what makes the visible action the identity.

## The static pass, as passes

The runtime check is emitted by a compile-time pass, written the
way a small compiler is: one module per pass, an explicit form between each
pair, and an interpreter for every form.

```
            cut            park              resolve            decide
  source --------> Cut ----------> Parked -----------> [Record] ---------> table
  S/Pass/Cut.hs    S/Pass/Park.hs  S/Pass/Resolve.hs   S/Pass/Decide.hs
```

`cut` splits the program at its first lift. `park` runs the lift-free prefix
on the test inputs and factors it as `g (x) B`, a constant temporary beside a
visible action. `resolve` turns each lift into a restriction of its register,
giving one lift-free program per record. `decide` runs each of those from `g`
and factors at the drop. A pass that cannot establish its hypothesis declines
by name: `prefix-parks` in `park`, `B-right-invertible` in `resolve`.

Every form means the same state at the drop site. `S.Pass.chain` lists those
meanings in order, so the `passes` group (`src/S/Test/Pass.hs`) checks that
the passes preserve the program by walking one list, over every drop site,
record and test input. `dqt pass file.s` prints the stages and the emitted
table beside the criterion's answer.

## Reading order

1. `src/DQT/Algebra/`: `Scalar.hs` and `Linear.hs`, the exact field and the
   matrices. Everything else is arithmetic-free.
2. `src/DQT/Calculus/`: `Syntax.hs` and `Typing.hs`, the calculus and its one
   scope premise; then `Elaborate.hs` and `Machine.hs`, the two semantics and
   the check that they agree.
3. `src/DQT/Criterion/`: `Split.hs` and `Gram.hs` with `src/DQT/Criterion.hs`,
   the criterion by two routes that must decide alike; then `Witness.hs`, the
   converse as an algorithm that emits source.
4. `src/DQT/Many/`: many temporaries, and what per-temporary release costs.
5. `src/DQT/Lifted.hs` and `src/DQT/Residual.hs`: dynamic lifting, and the
   runtime check that replaces the static one.
6. `src/DQT/Corpus/Classical.hs`: the same obstruction with the physics removed.
7. `src/S/Lang/`: `Syntax.hs`, `QState.hs`, `Interp.hs`, the second
   implementation, with the criterion as a test rather than a rank.
8. `src/S/Pass/` and `src/S/Pass.hs`: the static pass, one module per pass,
   and the chain they form.
9. `src/DQT/Bridge.hs`: the two, compared.
10. `programs/SYNTAX.md`, then any `.s` file: the concrete syntax.

Every check in `test/Spec.hs` is named after the statement it decides, so the
list of check names is the list of claims.
