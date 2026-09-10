# `Drop`: the criterion, in Lean

A Lean 4 library over Mathlib. It mechanises the central theorem — *a typed
program is weakenable exactly when its drop is safe* — from the syntax of the
calculus up, together with the linear algebra the rest of the development
rests on. Twenty files, no `sorry`, and no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`; `Drop/Audit.lean` prints them.

The path through it: `SimpleTensor` builds the joint register, `Circuit/` and
`Source/` build a program's output map and define drop safety on it,
`Calculus/` adds the affine syntax and typing, and `Calculus/Reflection.lean`
closes the loop with `typed_weakening_iff_discardSafe`. `Dilation/` says the
same thing again in the language of dilations. `Gram`, `Marginal`, `Local`,
`Boundary` and `Robust` hold the core facts the paper quotes.

Scalars are real in the calculus files.  Below them they are an arbitrary
`RCLike` field, except that `Gram` and `Marginal` need only a commutative
star-ring and `Local` only a commutative ring, `Robust` and
`Dilation/Program` fix the reals, and
`Boundary` carries no scalar at all.

Not mechanised: the measurement fragment, the composite temporary, the
complexity results and the gate-set analysis. The Haskell checker computes
the verdicts for those.

```
lake exe cache get   # Mathlib's compiled files
lake build
```
