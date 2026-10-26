# Reading the OpenQASM emitter

Start at `compileWith` in `src/Drop/Lang/Compile.hs`.
It makes four decisions in order, one module each:

1. `layoutProgram` (`src/Drop/Lang/Compile/Layout.hs`) checks the fragment and gives every register physical
   qubit indices. It also assigns measurement bits and records how many
   lifts precede each drop.
2. `fragmentSafety` (`src/Drop/Lang/Compile/Safety.hs`) decides each drop on each reachable record, using exact
   arithmetic. Its table contains a fixed temporary line, a loan factor,
   an unsafe verdict or an unreachable record.
3. `reuseLayout` (`src/Drop/Lang/Compile/Reuse.hs`), used only by `compile-reuse`, assigns safely returned whole
   temporary blocks to a common pool. A block must be basis-allocated and
   safe on every reachable record. Its return must be emitted or the identity;
   a numerical refusal aborts compilation. Inputs and loans keep their wires.
4. `compileTerm` (`src/Drop/Lang/Compile/Emit.hs`) emits source gates and inserts supported local returns.
   `buildHeader` and `outputMeasureLines` add declarations and measurements
   of the registers the source returns.

The command `dqt allocation program.s` shows the connection between these
steps: physical wires in both layouts, the exact certificate, inserted gates
and whether each block enters the pool. Begin with this report when a circuit
looks surprising.

## A drop and a return gate do different jobs

A source `drop t` forgets a name. It does not erase a state. If `t` was
allocated at `|0>` and now holds `|+>`, the emitter inserts a gate equivalent
to H on that wire. The independent data computation is left alone.

For a larger block, `emitReclaim` selects an identity, a basis permutation,
a two-support reflection or the general reflection. The general construction
runs the inverse axis preparation, flips the sign of `|0...0>`, then runs
the axis preparation. A block that holds loans gets the return gate T with
T B = J from `emitLoanReturn`, which builds the general case with `emitFrameReturnOps`: one reflection per column of the block
factor B, each carrying that column onto the loan's basis state beside the
temporaries' allocation state and fixing the columns already placed, then one
diagonal that removes the unit scalars. `frameReturnMatrix` is the same gate
as a matrix, which the leaf reference applies.
`Op` describes these gates before text rendering; `renderOp` prints them.
This keeps the matrix construction separate from wire spelling.

The real rotations inside that preparation print as controlled `ry(theta)`.
They must not print as controlled `U(theta,0,0)`: OpenQASM3's built-in U adds
`exp(i*theta/2)`, which becomes a relative phase when controlled. For general
Euler angles the renderer uses, in circuit order, `p(lambda); ry(theta);
p(phi)` with the same controls. Uncontrolled U gates may retain an overall
phase; a preparation and its adjoint cancel that phase. An unpaired U, as
in a one-qubit return, retains its common phase. The compiler applies no
quantum control around these complete returns; a tool that adds it needs
to account for that phase.

Gate definitions: [OpenQASM3 U and controls](https://openqasm.com/versions/3.0/language/gates.html#built-in-gates)
and [standard p/ry gates](https://openqasm.com/language/standard_library.html).

## What is supported

The emitter handles qubit registers, the named gates recognized by
`recognizeGate`, diagonal gates, basis permutations and one-qubit unitaries.
Basis allocations assume zero scratch and emit X gates as needed. A non-basis
allocation is refused as outside the compilation fragment. The fragment forbids allocations, lifts and drops inside
conditional branches. Declared gates outside the lowering table are refused.

A loan starts in an unknown caller state. Every safe loan block is returned
on the block; the caller's loan is not measured as a returned value. The
identity, a one-qubit unitary and a basis permutation keep their short forms,
alone or beside the temporaries' certificate; every other isometric block
factor, square or rectangular, gets the reflections-and-diagonal return gate
above. Loan drops after a lift or conditional are refused.
A mixed loan/temporary drop does not enter the temporary pool.

A source record bit means survival of a selected subspace. Its value need not
be the raw QASM measurement bit. `liLiftInfo` records that translation; emission
must use it when writing a condition.

## Checking a change

Build with `cabal build exe:dqt`, then obtain its path with
`cabal list-bin exe:dqt`. From `../qasm3`, use that executable with:

```sh
python emission_check.py --dqt /absolute/path/to/dqt
python reuse_check.py --dqt /absolute/path/to/dqt --programs ../haskell/programs
```

These checks parse emitted OpenQASM and compare with independently specified
maps. They retain record weights and caller references. The controlled-return
fixture also inspects all scratch wires: a wrong return must not disappear
merely because an unreturned temporary was traced out. `compile_check.py`
compares with machine-generated leaves and shares factor extraction with the
compiler; it supplies a different check, with that dependence kept explicit.

Exact safety decisions and numerical gate synthesis are separate. Passing
these finite tests is not a compiler correctness proof or a certified bound
on angle error. A general refinement from the proved pooling machine to this
restricted emitter remains work to do.
