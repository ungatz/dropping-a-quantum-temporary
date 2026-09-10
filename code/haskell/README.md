# The affine drop calculus, and its checker

When may a quantum temporary be dropped? The package answers that twice, with
two implementations that share no code, and `DQT.Bridge` runs them against
each other. They do share one exact scalar backend, so the comparison varies
the algorithm and holds the arithmetic fixed; it is less than two wholly
independent implementations.

`src/DQT` builds the denotation `K : H_m -> H_d (x) H_m` as a matrix, forms
its Kraus operators, and takes an exact rank. `src/S` never builds `K`: it
runs the program on `dim + 1` test inputs, factors the state at the drop
site, and asks whether the lines agree. They agree on every catalogue verdict
and every runtime-check entry.

Arithmetic is exact everywhere — the theory layer over `Q(w)` for `w` a
primitive eighth root of unity, the language layer up the tower `Q`,
`Q[sqrt2]`, `Q(zeta_{2^k})`. A check walks the sources and fails if any
inexact numeric type appears anywhere.

## Running it

Everything runs on `base` alone (the check suite also uses `directory`), so
nothing needs installing beyond GHC:

```
runghc -isrc test/Spec.hs                        # the whole check suite
runghc -isrc app/Main.hs                         # the subcommand list
runghc -isrc app/Main.hs all                     # every report at once
runghc -isrc app/Main.hs run   programs/mcx-dirty.s
runghc -isrc app/Main.hs trace programs/dj.s     # the run, frame by frame
runghc -isrc app/Main.hs pass  programs/tilt.s   # the static pass, stage by stage
```

or `cabal build && cabal test`.

## Where things are

`src/DQT/` holds the theory layer: `Algebra/` the exact field and matrices,
`Calculus/` syntax, typing and the two semantics, `Criterion/` the criterion
by two routes and its converse, `Many/` several temporaries, `Lifted.hs` the
calculus with measurement, `Residual.hs` the runtime check over it.

`src/S/` holds the language layer: `Lang/` the surface syntax, scalars,
states, parser and interpreter; `Pass/` the static pass, one module per pass;
`Programs/` the corpus; `Report/` what the command line prints.

`programs/` is the surface corpus as `.s` files, with `SYNTAX.md` as the
one-page reference. `test/Spec.hs` runs one named check per statement. The
Silq programs of the comparison are in `../silq/`.

## Reading it

Start at `programs/SYNTAX.md` and any `.s` file, then `S/Lang/Interp.hs`,
which is the criterion in twenty lines. `S/Pass.hs` explains the four passes
and the table they emit. `DQT/Criterion/Gram.hs` is the same verdict taken
the other way.
