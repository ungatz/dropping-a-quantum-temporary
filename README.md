# Dropping a quantum temporary: the artifact

When may a quantum temporary be dropped, and what does deciding it cost?
Three directories:

```
haskell/   the checker: the calculus, its two semantics, the drop criterion by
           two independent routes, the static pass that emits the runtime
           check, and the check suite that pins every number it reports
lean/      the linear-algebra core, proved in Lean 4 over Mathlib
silq/      the Silq programs of the comparison table, with the transcripts
           the Silq build printed on each of them
```

## The checker (`haskell/`)

Everything runs on `base` alone (the check suite also uses `directory`), so
nothing needs installing beyond GHC:

```
cd haskell
runghc -isrc test/Spec.hs             # the whole check suite, about fifteen minutes
runghc -isrc app/Main.hs all          # the whole report
runghc -isrc app/Main.hs run programs/mcx-dirty.s
runghc -isrc app/Main.hs pass programs/tilt.s   # the static pass, stage by stage
```

or, compiled, `cabal build && cabal test` from the same directory.
`haskell/README.md` has the reading order, the table of every printed
number and the function that computes it, and the catalogue of verdicts.

## The proofs (`lean/`)

A library, `Drop`, over Mathlib (Lean `v4.28.0`, Mathlib pinned in
`lean/lakefile.toml`): twenty files, no `sorry`, no axiom beyond the three
standard ones. It mechanises the criterion end to end, from the syntax and
typing rules to the theorem that a typed program is weakenable exactly when
its drop is safe. `lean/README.md` maps each file to what it holds, and says
what is not proved there.

```
cd lean
lake exe cache get      # fetch the Mathlib build once
lake build
```

## The Silq comparison (`silq/`)

Reference material, not part of any build: the `.slq` programs, the driver
script `run_silq.sh`, and `TRANSCRIPT.md`, which records what Silq printed on
each program.
