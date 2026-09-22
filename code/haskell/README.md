# A typed language for quantum temporaries, and its checker

**When may a quantum temporary be dropped?** A drop is *safe* when the
temporary's block of the site map factors as `g (x) W` — one ray `g` for the
block, one map `W` for everything else. This package decides that, exactly,
and compiles the programs it decides to OpenQASM 3.

It answers the question **twice, by two different algorithms**, and checks the
two answers against each other.

```
cabal test                     # the three suites
cabal run dqt -- all           # every report, in the paper's order
cabal run dqt -- list          # the theory engine's catalogue, one line per program
cabal run dqt -- run     programs/mcx-dirty.s
cabal run dqt -- compile programs/dj.s
```

`dqt list` is the catalogue the paper's implementation section cites; it is the theory
engine's own seventeen programs, a different set from the nineteen `.s` files of
`programs/`.

No build needed: the library uses only `base` and `containers`, the suites also
`directory`.

```
runghc -isrc app/Main.hs            # the subcommand list
runghc -isrc test/Spec.hs           # the named statements
```

## The map

```
src/Drop/Lang/     THE LANGUAGE.  The language of the paper: its syntax, its two
           judgements, its five-rule machine, its elaboration, its compiler
           to OpenQASM 3 -- and the LANGUAGE ENGINE, which decides a drop by
           factoring states from probe inputs at temporary sites. For a block
           holding loans, it builds and factors the map on the loan inputs and
           the other inputs, then checks that the loan factor is an isometry.

src/Drop/Theory/   THE THEORY ENGINE.  Builds the site map K as an explicit matrix,
           decides proportionality of its Kraus blocks by the exact rank of
           their coefficient matrix. It also computes Gram and Choi matrices.
           It has its own program representation and fixtures, and imports
           no language-layer module.

src/Drop/Bridge.hs   the seam: it translates a theory-engine program into a
                    language-engine one and compares the verdicts.
```

| file or directory | what it is | in the paper |
| --- | --- | --- |
| `src/Drop/Lang/Typed.hs` | types, values, statements, terms | the syntax figure |
| `src/Drop/Lang/Check.hs` | the two judgements, errors carrying the line | the statics subsection |
| `src/Drop/Lang/Machine.hs` | the five rules, on `<Delta, sigma \|\| M>` | the dynamics subsection |
| `src/Drop/Lang/Elab.hs` | elaboration to the flat command list | the denotation subsection |
| `src/Drop/Lang/Compile.hs` | the compiler to OpenQASM 3, and its domain | the compilation subsection |
| `src/Drop/Lang/Interp.hs` | the language engine: probe, factor at the site | the criterion section |
| `src/Drop/Lang/Parser.hs` | the `.s` concrete syntax | `programs/SYNTAX.md` |
| `src/Drop/Lang/{Cyclo,Ring,Gates,QState,Syntax}.hs` | scalars, gates, states, the flat form | — |
| `src/Drop/Lang/Pass/` | the compile-time pass that emits the per-record table | the record-dependent reclaim section |
| `src/Drop/Lang/Programs/` | the algorithms as Haskell values, one module each | the corpus table |
| `src/Drop/Lang/Report/` | what `dqt run` / `trace` / `pass` print | — |
| `src/Drop/Lang/Checks/` | the language layer's own checks | — |
| `src/Drop/Theory/Algebra/` | the exact field `Q(zeta_8)`, and matrices | — |
| `src/Drop/Theory/Program/` | the theory engine's program representation and its two semantics | — |
| `src/Drop/Theory/Criterion/` | the criterion by two routes, its converse, and contexts | the criterion section, the contextual-equivalence subsection |
| `src/Drop/Theory/Many/` | several temporaries: bundling, and the ring conditions | the composite-temporary proposition, the gate-ring section |
| `src/Drop/Theory/Lifted.hs` | measurement, and the verdict per record | the measurement section |
| `src/Drop/Theory/Residual.hs` | the per-record table as emitted data | the record-dependent reclaim section |
| `programs/` | the corpus: 19 `.s` programs. `SYNTAX.md` is the one-page reference | the corpus table |

Names in the last column are the paper's `\label`s. They are used instead of
section numbers on purpose: a label survives a renumbering, a number does not.

## Why two engines

The theory engine and the language engine decide the same question by
different means, and `dqt bridge` reports any site where they disagree. They
**share the scalar field** — the language layer is polymorphic over
`(Eq a, Fractional a)` and the bridge runs it at the theory layer's exact `K` —
so the comparison holds the arithmetic fixed and varies only the algorithm.
That is less than two wholly independent implementations, and it is what the
comparison is worth.

Verdict arithmetic is exact. The theory layer works over `Q(w)` with
`w = exp(i*pi/4)` a primitive eighth root of unity; the language layer works
over the smallest field that states each program, up the tower `Q`,
`Q[sqrt2]`, `Q(zeta_{2^k})`. A source check rejects inexact numeric types
outside the numerical gate emitter and its test. Emitted angles do not
feed back into a verdict.

## The three suites

| suite | what it checks | size |
| --- | --- | --- |
| `dqt-test` | the paper's claims, one named statement each, over both engines | 44 statements, plus the language layer's own 279 checks in 15 groups over 10 algorithms |
| `dqt-typed-test` | the language: the corpus typechecks; the machine agrees with the denotation; progress and preservation on random terms; the desugaring lemma; `Sigma_o E_o^dagger E_o = I`; the site definition adversarially (loans, tuple blocks, unreachable records); the loan discipline; `Step-New`'s capture side condition; the termination bound `\|M\|`; the hidden-register invariant; `drop ()`; the block on the corpus | 90 checks |
| `dqt-compile-test` | the compiler: which corpus programs compile; the reclaiming reflection with its `U(theta,phi,lambda)` and its general `k`-qubit cascade; the three square block factors it can lower, and the mixed block of product form; `drop ()`; a tuple dropped out of allocation order. Writes the circuits and leaf amplitudes to `../qasm3/out-typed/` | 317 checks |

`dqt-compile-test` writes the files `../qasm3/compile_check.py` reads, so run
`cabal test` before it.

Every statement in `test/Spec.hs` is named after the claim it decides, so the
list of names is the list of claims.

## Every printed number, and what computes it

None is transcribed by hand.

| number | computed by | pinned by |
| --- | --- | --- |
| the verdict of every example program | `Drop.Theory.Criterion.verdict` | `the-verdicts-are-the-expected-ones` |
| the two engines give the same verdict at every site | `Drop.Bridge.bridgeDisagreements` | `the-two-engines-agree`, `the-residual-pass-is-exhaustive-and-agrees` |
| a loan's verdict: the site map factors as `B (x) W` with `B` an isometry, not as a fixed ray | `Drop.Lang.Interp.loanResultS` | `dqt-typed-test` (g), (l) |
| a block holding loans beside temporaries: the site definition's clause (4) with `B` rectangular | `Drop.Lang.Interp.loanResultS` | `dqt-typed-test` (g), (j); `dqt-compile-test` (h) |
| every loan input is dropped exactly once, and a loan is never returned | `Drop.Lang.Check.loanDiscipline` | `dqt-typed-test` (l) |
| `Step-New` refuses a name bound later in the term | `Drop.Lang.Machine.stepNewAt` | `dqt-typed-test` (n) |
| every run reaches a value in at most `\|M\|` steps | `Drop.Lang.Typed.termSize` | `dqt-typed-test` (o) |
| expanding a block changes no state at any site, hence no verdict | `Drop.Lang.Typed.seqTerm`, `toTerm` | `dqt-typed-test` (q) |
| the per-record table: refuse on the block {0,1}, accept on {2} | `Drop.Theory.Residual.residualCheck`; `Drop.Lang.Pass`, printed by `dqt pass programs/rus.s` | `the-residual-table-agrees-with-the-semantic-criterion` |
| the Bell pair is safe jointly and unsafe register by register | `Drop.Theory.Many.Multi.jointSafe`, `everyWireSafe` | `joint-safety-is-strictly-coarser-than-per-wire-safety` |
| the ring witnesses of the reclaiming proposition | `Drop.Theory.Criterion.Witness.householder`, `Drop.Theory.Many.Nested.nestedWitness` | `carrying-a-unit-vector-is-necessary-not-sufficient`, `the-obstruction-is-that-two-is-not-a-square` |
| one qubit temporary, two records at weight 1/2, opposite verdicts | `Drop.Theory.Lifted.verdictProfile` | `a-scratch-qubit-splits-once-a-joint-gate-follows-the-lift` |
| two programs with one channel, equal branch weights, opposite verdicts | `Drop.Theory.Lifted.coreMapAt`, `Drop.Theory.Criterion.Gram.choiMatrix` | `the-summed-channel-does-not-decide-the-drop` |
| the `C3X` borrowed-loan lines: `B = I`, `B = X` after an extra flip, refused once the fourth Toffoli is deleted | `Drop.Lang.Report.Run.runText` on `programs/mcx-dirty*.s` | `the-borrowed-loan-returns-via-a-fixed-gate` and two more |
| 16 of the 19 corpus programs compile; `rus.s` is refused by dimension, `bell-block.s` and `c.s` for a gate outside the table | `Drop.Lang.Compile.compile` | `dqt-compile-test` (a), (b) |
| 173 leaves, over the 16 compiled corpus programs and 7 compiler fixtures, agree with the machine up to a global phase per leaf | `../qasm3/compile_check.py` against `out-typed/*.leaves.json` | the checker's own last line |
| no inexact numeric type occurs in 60 of the package's 62 source files | `test/Spec.hs` `floatCheck` | `no-floating-point-anywhere` |

## The corpus

`programs/` holds 19 `.s` programs; the corpus table in the paper's implementation section lists
every one with its sites, records, verdicts, certificates and reclaiming gates.
Each file's own header states its expected verdict, and the suites check it.
Three turn on a measurement:

* `shor.s` (order finding, `N = 15`, `a = 7`): unmeasured the residue register
  is unsafe; measured, safe on the block `{7}` and unsafe on its complement.
* `simon.s` (hidden string `11`): unmeasured unsafe; measured, safe on both
  records but on different lines, since `f` takes only the values 0 and 1.
* `temp-and.s` (measurement-based `AND` uncompute): unmeasured unsafe; with
  `H`, a measurement and the `CZ` correction, safe on both records — and the
  correction is what makes the visible action the identity.

## The per-record table, as a pass

The runtime table is emitted by a compile-time pass, written the way a small
compiler is: one module per pass, an explicit form between each pair, and an
interpreter for every form.

```
  source ---> Cut ---> Parked ---> [Record] ---> table
             Cut.hs   Park.hs     Resolve.hs    Decide.hs

  Pass modules: src/Drop/Lang/Pass/
```

`Cut` splits the program at its first measurement. `Park` runs the
measurement-free prefix on the probe inputs and factors it as `g (x) B`.
`Resolve` turns each measurement into a restriction of its register, giving one
measurement-free program per record. `Decide` runs each from `g` and factors at
the drop. A pass that cannot establish its hypothesis declines by name. Every
form means the same state at the drop site; `Drop.Lang.Pass.chain` lists those meanings
in order, and `src/Drop/Lang/Checks/Pass.hs` checks the passes preserve the program by
walking one list over every drop site, record and probe input.

## Reading order

1. `src/Drop/Lang/Typed.hs`, then `Check.hs` — the language and its statics. A
   term is a sequence of statements ending in `return`. `new` binds a
   register; `lift` binds a classical parameter. `seqTerm` expands a block
   by binding its returned names in the continuation.
2. `src/Drop/Lang/Machine.hs` — the five rules; then `Elab.hs` and `Interp.hs`.
3. `src/Drop/Lang/Compile.hs` — the compiler, and the domain it states.
4. `src/Drop/Theory/Algebra/` — the exact field and the matrices. Everything else in
   `src/Drop/Theory/` is arithmetic-free.
5. `src/Drop/Theory/Criterion/` — `Split.hs` and `Gram.hs` with `Criterion.hs`: the
   criterion by two routes that must decide alike; then `Witness.hs`, the
   converse as an algorithm that emits source.
6. `src/Drop/Theory/Lifted.hs` and `Residual.hs` — measurement, and the per-record
   table; then `src/Drop/Bridge.hs`, the two engines compared.
7. `programs/SYNTAX.md`, then any `.s` file.

The OpenQASM 3 checker and the reuse benchmark are in `../qasm3/`; the Silq
programs and their transcripts are in `../silq/`, reference material and not
part of this build.
