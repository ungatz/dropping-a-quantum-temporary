# `Drop`: the criterion, in Lean

A Lean 4 library over Mathlib. It mechanises the central theorem, from the
syntax of the calculus to *a typed program is weakenable exactly when its
drop is safe*, with the linear algebra the rest of the development rests on.
Twenty files, no `sorry`, no axiom beyond `propext`, `Classical.choice` and
`Quot.sound`; `Drop/Audit.lean` prints them.

## The criterion

Read in this order.

| file | what it holds |
| --- | --- |
| `Drop/SimpleTensor.lean` | the joint register `EuclideanSpace 𝕜 (ι × μ)`, simple tensors `tens g b`, the two contractions, `‖g ⊗ b‖ = ‖g‖ ‖b‖` |
| `Drop/Circuit/Output.lean` | a compute side `P : ι → Matrix μ μ 𝕜` and its output map `v ↦ ∑ᵢ eᵢ ⊗ P i v`; post-selection of the temporary on `g` is contraction against `g`; an isometric compute side preserves the norm |
| `Drop/Source/Language.lean` | bodies (`halt`, `gate U ; body`), well-typedness (`Uᴴ U = 1`), the denotation of `alloc i₀ ; p`, and the extraction: that denotation is the output map of the column block of the circuit at the allocated value |
| `Drop/Source/Gates.lean` | permutation gates and local gates `V ⊗ W`, and how running them composes |
| `Drop/Source/Safety.lean` | `DiscardSafe i₀ p`: the temporary ends in one fixed unit state `g` and the visible register receives one fixed map `W`. `discardSafe_iff_temporary_fixed`: the drop is safe exactly when the temporary always ends in the same state, and then `W` is post-selection on it |
| `Drop/Source/Reflection.lean` | a matrix that acts isometrically is unitary; the Householder reflection `reflectionTo i₀ g` that carries `e_{i₀}` to any unit `g`, with `g = e_{i₀}` giving the identity, which is what closes the reverse direction of `typed_weakening_iff_discardSafe` |
| `Drop/Calculus/Syntax.lean` | the affine calculus: `let a = new i₀ in t`, `let (a', v') = U (a, v) in t`, `drop a ; t`, values; elaboration to a body |
| `Drop/Calculus/Typing.lean` | the typing rules; a typed program elaborates to a well-typed body and denotes an isometry |
| `Drop/Calculus/Machine.lean` | the operational semantics and its agreement with the denotation |
| `Drop/Calculus/Reflection.lean` | `SourceWeakenable P`: some typed program of the shape `sep(R, W)` has the same denotation. **`typed_weakening_iff_discardSafe`**: for a typed program, weakenable ⟺ drop-safe. `sourceWeakenable_iff_discardSafe_and_isometric`: without typing the missing clause is exactly norm preservation |
| `Drop/Dilation/Dilation.lean`, `Bridge.lean`, `Program.lean` | the same criterion in the language of dilations: a program read as a map into `temporary ⊗ visible` is drop-safe exactly when an isometry on the temporary alone can erase it (`typed_weakening_iff_erasable`) |

Scalars are real in the calculus files and an arbitrary `RCLike` field in the
files before them.

## The core

| file | what it holds |
| --- | --- |
| `Drop/Gram.lean` | the Gram matrix `Γᵢⱼ = tr(Kᵢᵀ Kⱼ)`; for `K = g ⊗ W` it is `m · g gᵀ`, so `Γ² = m Γ` |
| `Drop/Marginal.lean` | `Tr_v [K Kᵀ] = Γᵀ`: the temporary's state at the maximally mixed input is `Γᵀ/m` |
| `Drop/Local.lean` | local procedures compose as Kronecker products and act as products |
| `Drop/Boundary.lean` | the exact boundary, in the abstract (`exists_recordExact_iff`): a class of commands admits a record-oblivious verdict that is record-exact on it exactly when no command of the class has two reachable records of opposite verdict |
| `Drop/Robust.lean` | the scalar inequalities of the robustness bounds |

## What is not here

The measurement fragment, the composite temporary, the complexity results and
the gate-set analysis are not mechanised. The Haskell checker in
`../haskell/` computes every verdict for them.

## Building

```
lake exe cache get   # Mathlib's compiled files
lake build
```

`lean-toolchain` pins Lean; `lakefile.toml` pins the Mathlib commit.
