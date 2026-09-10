# The `.s` concrete syntax

**Which S this is.** The language this checker reads: `new`, `newdirty`,
`gate`, `lift`, `if` and `drop`. There is deliberately no `release` statement
and no `borrow` statement. The calculus records what the free pool *receives*
when a drop is admitted -- a certificate naming the dimension and the ray --
and adds no construct for taking one back out, so neither does this grammar.
(`borrow` and `release` exist in `DQT.Many.Release` as operations *on* the
pool; they are not constructs of this language.) A program that needs a
register on a state it did not prepare writes `newdirty`, which names the
state outright.

A `.s` file is the text form of the surface language S.  It parses
(`S.Lang.Parser.parseProgram`) to a pair of a visible-register spec and a program
over the exact scalar field Q(ζ₁₆); there is no floating-point syntax to write
down.  `--` starts a comment anywhere on a line, whitespace is free within
lines, and `;` terminates statements.  Every parse error carries a line
number, and there are no silent defaults.

## Grammar

```
program  ::= visline stmt*
visline  ::= 'vis' name ':' nat (',' name ':' nat)* ';'   -- required first statement

stmt     ::= 'new' name ':' nat ';'                       -- allocate at |0> (nat is the dimension, >= 2)
         |   'newdirty' name ':' nat '@' '(' scalar (',' scalar)* ')' ';'
                                                          -- dirty ancilla on that unit state
         |   'gate' GATE name+ ';'                        -- named unitary, first name most significant
         |   'phase' '(' scalar ')' name+ ';'             -- 1 register: diag(1,s); 2: diag(1,1,1,s)
         |   'mat' name+ '{' row (';' row)* [';'] '}' [';']
                                                          -- general exact d x d matrix, row by row
         |   'diag' name+ '(' scalar (',' scalar)* ')' ';' -- diagonal matrix, d entries
         |   'perm' name+ '(' nat+ ')' ';'                -- permutation |j> -> |p_j>, d images
         |   'lift' name '=' 'meas' name 'in' '{' nat (',' nat)* '}' ';'
                                                          -- measure the block, bind the outcome bit
         |   'if' name '{' stmt* '}' 'else' '{' stmt* '}' [';']
                                                          -- classical control on a lifted bit
         |   'drop' name ';'                              -- the construct under study

row      ::= scalar (',' scalar)*
GATE     ::= H | HC | X | Z | CX | CCX | Swap | T | S | tilt | READ3 | Diff
```

`mat`, `diag` and `perm` are the general gate literal: any exact matrix on the
named registers, with `d` the product of their dimensions, checked at parse
time.  `diag` and `perm` expand to the same node `mat` produces, and `perm`'s
image list must be a permutation of `0..d-1`.  Matrices are taken exactly as
written; `S.Report.Run` refuses a program containing one that is not unitary
(`U U^H = I`, tested exactly): the criterion is stated for unitary
computations.

`renderProgram` emits a named gate when the matrix is in the table, otherwise
`diag` or `perm` when the matrix is diagonal or a permutation, otherwise
`mat`.  Rendering a program and parsing the result returns the program: the
round trip is the identity on abstract syntax, not on text, since a gate with
two names in the table renders under the first and comments do not survive.

## Gates

| name | dimension | matrix |
|---|---|---|
| `H`, `HC` | 2 | Hadamard over the tower, with 1/√2 = (ζ₈+ζ₈⁻¹)/2 |
| `X`, `Z` | 2 | Pauli |
| `T`, `S` | 2 | diag(1, ζ₈) and diag(1, i) |
| `CX` | 2·2 | control first: \|c t⟩ → \|c, t+c⟩ |
| `CCX` | 2·2·2 | Toffoli on (c₁ c₂ t) |
| `Swap` | 2·2 | swap |
| `tilt` | 3 | ⅓·[[2,2,1],[2,−1,−2],[1,−2,2]] |
| `READ3` | 3·3 | \|x t⟩ → \|x+t mod 3, t⟩ |
| `Diff` | 2·2 | Grover diffusion 2\|s⟩⟨s\| − I |

The named registers' dimensions must multiply to the gate's dimension,
registers may not repeat within one gate, and `phase` requires 2-dimensional
registers.

## Scalars

```
scalar   ::= product (('+'|'-') product)*
product  ::= factor ('*' factor)*
factor   ::= '-' factor
         |   'i'              -- zeta_4
         |   'z8'  ['^' nat]  -- zeta_8 ^ j
         |   'z16' ['^' nat]  -- zeta_16 ^ j
         |   nat              -- integer
         |   nat '/' nat      -- exact rational
         |   nat '/' 'rt2'    -- n * (1/sqrt 2)
```

Examples: `3/5`, `-1/2`, `z8^3`, `i`, `1/rt2`, `3/5*z8`, and
`1/2*z8-1/2*z8^3`, which is 1/√2 spelled out.  Nothing else: no floats, no
parentheses inside a scalar, no radicals beyond the tower.

## Running a program

A program runs against the visible registers of the `vis` line and a
**selection**: one bit per `lift` in run order, `1` meaning the measured block
survives and `0` its complement.  States are exact and unnormalized, so each
selection's weight is an exact scalar, for example 8/9 against 1/9 in `rus.s`.

`drop` is denotationally the identity.  Whether it is *safe* is the
criterion's question, answered per drop site and per selection.  `S.Report.Run`
answers it:

```
runText   :: String -> Either String Report   -- pure: parse, run, report
runFile   :: FilePath -> IO ()                -- the same over a file, printed
```

## Static checks at parse time

Unknown gate or statement names; malformed scalars; unknown, duplicate or
repeated registers; a gate's dimension against the registers it names; a
`newdirty` amplitude count against the declared dimension, and its norm
(‖ψ‖² = 1, exactly, since every construct of the language is an isometry);
`lift` block basis states in range, distinct and nonempty; `if` on a bit that no
`lift` has bound.

Three scoping rules go with them, and each is the calculus read at the surface.

*One binder per name.*  A dropped name leaves the live set, so a later
statement naming it fails, and it cannot be allocated again either: `drop` is
denotationally the identity, so the wire is still there, and a second `new t`
would leave two wires answering to `t` of which only the first is ever found.
Reusing the wire is the allocator's business, and the allocator is outside
this language.  A lift parameter is likewise bound once, as the calculus
writes them --- `p0`, `p1`, and so on.

*Only a temporary is dropped.*  The visible registers are the ones named on
the `vis` line.  They are the observer the criterion is about, and the core's
`drop` rule cannot be applied to them.

*An `if` branch binds nothing.*  The calculus types both branches of a
conditional at the same parameter count and under the same flag, so no `new`,
`newdirty`, `lift` or `drop` may appear inside one.  Every analysis
downstream reads the binders off the top-level statement list; a branch-local
binder would be checked by nothing while its name stayed live outside the
branch.

## A worked example

`programs/tilt.s`, the program the boundary result is proved with:

```
vis x:3;
new t:3;
gate tilt t;
lift p = meas t in {0,1};
gate READ3 x t;
drop t;
```

One visible qutrit `x`; a temporary `t` allocated at |0> and tilted to
(2/3, 2/3, 1/3), which has a foot inside the measured block {0,1} and a foot
on |2>; a lift of that block; a read that adds `t` into `x`; and the drop.

Selecting the block, weight 8/9, leaves `t` in a superposition that the read
correlates with `x`, so the drop is refused.  Selecting the complement,
weight 1/9, leaves `t` on the basis line |2>, the read is a constant shift,
and the drop is accepted.  Two selections, one program text, opposite
verdicts:

```
drop t (depth 1):
  trace 1     Inadmissible
  trace 0     Admissible    line (0,0,1)
```

## The shipped programs

| file | what it is |
|---|---|
| `dj.s` | Deutsch-Jozsa with the \|−⟩ ancilla |
| `bv.s` | Bernstein-Vazirani, hidden string 11 |
| `grover.s` | one Grover iteration, compute-phase-uncompute |
| `qpe.s` | phase estimation of T, three counting qubits |
| `superdense.s` | superdense coding of the pair (1, 1) |
| `teleport.s` | teleportation, two lifts and two drops |
| `rus.s` | one repeat-until-success iteration, unrolled |
| `tilt.s` | the boundary program |
| `mcx-dirty.s` | C³X from four Toffolis and a dirty ancilla lent on \|0⟩ |
| `mcx-dirty-plus.s` | the same text with the loan on \|+⟩ |
| `mcx-dirty-half.s` | the same with the last Toffoli deleted: refused |
| `shor.s` | order finding, N = 15, a = 7, three counting qubits |
| `simon.s` | Simon's problem on two bits, hidden string 11 |
| `temp-and.s` | a temporary AND uncomputed by measurement |
| `temp-general.s` | the spooky-pebble measurement-based uncomputation, at f = AND |
| `temp-general-unpaid.s` | the same with the phase correction deleted |

Each states its expected facts in a header comment. `S.Test.Parser` holds every
file to two of them: it parses, and rendering then parsing it again returns the
same abstract syntax. The eleven with a defining module are held to that module
too -- same syntax, same verdicts, and for seven of them one exact number. The
three `mcx-dirty` files are held to the verdict and parked line their own
headers state, and the two `temp-general` files to nothing further.
