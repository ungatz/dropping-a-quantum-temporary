# The `.s` concrete syntax

A program is a sequence of statements ending in `return`; the grammar below
is the accepted `.s` file format. The parser is
`src/Drop/Lang/Parser.hs`; `dqt typecheck FILE` parses and typechecks a file,
and `dqt run FILE` reports its drop verdicts.

## The grammar

```
types    A ::= 1 | [d] | A * B          -- no register; a d-level register;
                                        -- two side by side (d >= 2)
values   v ::= x | () | (v1, v2)        -- a register name; nothing; a pair
terms    M ::= return v                 -- hand back the registers v names
             | U v ; M                  -- a gate on the registers v names,
                                        --   in that order
             | new t : [d] @ psi ; M    -- allocate t in the unit state psi
             | drop v ; M               -- forget the registers v names
             | p = lift[S] x ; M        -- measure whether x is in S;
                                        --   x stays live under its own name
             | if e { M1 } else { M2 }  -- classical control on a lifted bit,
                                        --   in tail position; a file may write
                                        --   statements after an if (the
                                        --   sequencing below), and its arms
                                        --   allocate, lift and drop nothing
guards   e ::= 0 | 1 | p | !e | e1 && e2 | e1 || e2

programs     prog f (x1 : [d1], ..., xn : [dn]) : A { M }
             -- an input may be marked `loan a : [d]`
```

`*` associates to the right, so `[2] * [2] * [2]` is `[2] * ([2] * [2])`, and
so do tuples. A guard is a bit constant `0` or `1`, a parameter a lift bound,
or a negation, conjunction or disjunction of guards. The file format writes
these connectives as `!`, `&&`, and `||`. `S` is a set of levels, `{0}`, `{0,1}`, `{7}`: a
non-empty proper subset of the register's levels. `psi` is a ket `|i>` or an
exact amplitude vector `(a0, ..., a_{d-1})`, which must be a unit vector.

A gate's arguments are listed in the order its matrix expects: `U v` acts on
the factors in the order `v` names them. Three spellings write a gate out
instead of naming one, and each is a `U v ;` statement:

```
mat v { row ; ... ; row }        -- an exact matrix
diag v ( s , ... )               -- a diagonal
perm v ( i ... i )               -- a permutation: |j> -> |i_j>
```

## One binder

`new` is the only binder of the language. A gate binds nothing: `CX x t;`
applies CX to `x` and `t`, in that order, and the two registers keep their
names. A `drop` binds nothing. A `lift` binds its parameter and leaves the
register live under its own name. Terms are identified up to renaming of the
names `new` binds, and a rule that needs a name fresh takes one.

There is therefore no pattern grammar. The only tuple that ever binds is the
tuple of names of a block, below, and substituting a tuple of names for a
tuple of names is a renaming.

## Two judgements

A register context `Omega` is a finite set of typed register names with
pairwise distinct names, and the comma `Omega1, Omega2` is defined only when
the two have disjoint domains. That one convention is the whole discipline:
no register is named twice, and none is discarded without a `drop`. Two
judgements share the one context,

```
Omega |- v : A              values
Pi ; Omega |- M : A         terms, with Pi the parameters in scope
```

with seven rules for the measurement-free forms (Var, Unit, Pair, Return,
Gate, New, Drop) and two more for the two the measurement section adds (Lift,
If). A statement is not a term of the language, and nothing types one alone.
A program `prog f (x1:[d1], ..., xn:[dn]) : A { M }` is the judgement
`x1:[d1], ..., xn:[dn] |- M : A`; an input marked `loan` is typed as any
other. The typing rules are implemented in `src/Drop/Lang/Check.hs`.

`Drop` carries no premise about safety: if it did, unsafe programs would not
be *expressible*, and the rules that reject them could not be compared. That
is the criterion's question, and `dqt run FILE` answers it, one site and one
record at a time.

## The block, and the sequencing operator

Two surface forms are expanded before typing, and one operator expands them.
Write `M1 (+)_ybar M2` for "run M1, bind the value it returns to the tuple of
names `ybar`, continue with M2", by recursion on M1 — one clause per
statement, and the same clause for all of them:

```
(return v)               (+)_ybar M = M[v/ybar]
(stmt ; M')              (+)_ybar M = stmt ; (M' (+)_ybar M)
(if e {M1} else {M2})    (+)_ybar M = if e {M1 (+)_ybar M}
                                      else {M2 (+)_ybar M}
```

A block

```
ybar = { ...; return v };
```

is `M1 (+)_ybar M2`, and a non-tail `if` — one with statements after it — is
`(if e {M1} else {M2}) (+)_ybar M`. The binder `ybar` is a tuple of names,
because that is the only pattern that ever occurs: a binder of register type
is a name and one of unit type is `()`. The last clause copies the
continuation into both branches, so the expanded term can be `2^k` times the
size of the file under `k` nested blocks; no run, site or verdict changes.
The parameters a block binds leave scope at its closing brace.

`Drop.Lang.Typed.seqTerm` is the operator, three clauses and no more;
`Drop.Lang.Typed.toTerm` discharges the one surface production that uses it.

## `drop`, and the loan header marker

The header is the input context: `x : [d]` is an ordinary input register, and
`loan a : [d]` is a register the program is handed in a state it does not
know and must hand back. A loan is typed and run as an input; the marker is
used by the safety checker and the compiler, which prepares nothing for it — it
is an input register of the emitted circuit. A loan is *dropped*, never
returned, and exactly once on every execution path.

A `drop` of a tuple is **one** site, not two. A tuple that holds a loan is
checked by the loan criterion, whatever else the block holds: writing the
input space as `[[Omega]] = H_loan (x) [[Omega']]` with `H_loan` the tensor
product of the spaces of the loans **in the block**, the site is safe when
the site map factors as `sigma_s = B (x) W` with `B : H_loan -> H_block` an
isometry and `W : [[Omega']] -> H_rest` linear. `B` is the block factor, and
it is *rectangular* when the block holds temporaries beside its loans. A
block of temporaries only is the case `H_loan = C`, where `B` is the unit
vector the temporaries are left on — the fixed-ray test.

An input without the `loan` marker may also be dropped. If the block contains
no loans, the checker tests for one fixed pure block state at every input,
as it does for temporaries. Dropping an untouched input fails this test;
moving its state into another register can make the drop safe. The compiler
refuses a reachable safe drop that names an ordinary input, because that
input has neither a declared allocation state nor a loan-return obligation.
An unsafe drop leaves its wires live, as for any other unsafe drop.

## The file

```
file    ::= decl* prog
decl    ::= gate NAME : A = gatelit ;
```

A file holds optional top-level gate declarations and then exactly one
program. Comments run from `--` to the end of the line. Whitespace is free;
`;` terminates a statement; the body's last line is `return v`.

An explicit-binding spelling of a statement — `t = new [d] @ psi;`,
`p = U v;`, `() = drop v;` — is a parse error naming the printed form
instead: the accepted language is exactly the printed grammar above.

## The gate table

`H`, `X`, `Z`, `S`, `T`, `CX`, `CCX`, `Swap`, `Diff` (Grover's `2|s><s| - I`),
each with its standard matrix. `HC` is a second name for `H`. `tilt` and
`READ3` are qutrit gates used by `rus.s`. The OpenQASM compiler supports
power-of-two register dimensions and the gate forms listed by its implementation;
three-level registers are outside its domain.

A declared gate joins the table for that file:
`gate V : [2] * [2] = mat { ... };` makes `V t q;` a gate statement.

## Scalars

Exact only; there is no float syntax. Integers and rationals `n/m`; `i`;
`z8` and `z16`, the primitive 8th and 16th roots of unity, with powers
`z8^3`; `n/rt2` for `n/sqrt(2)`; sums, differences and products of these.

## What the parser checks, with a line number

A name is bound once, and a dropped name is never bound again. A gate's
registers are distinct, known, and of the right total dimension. An
allocation's state is a unit vector of the right length. A lift's block is a
non-empty proper subset of the register's levels, and its parameter is fresh.
An `if` branch binds nothing — no allocation, lift, drop or block — and its
guard reads only bit constants and parameters in scope. Every register is dropped or returned,
and the value returned has the type the header declares.

What it does not check is safety, for the reason `Drop` carries no premise.

## Running it

```
dqt typecheck FILE     parse and typecheck: prints `ok FILE: prog f : A`
dqt run FILE           the verdict at every drop site, on every record,
                       with the certificate or the reclaiming gate
dqt trace FILE         the run frame by frame, one temporary at a time
dqt pass FILE          the static pass behind the runtime check, stage by stage
```

## The files

| file | what it is | site, verdict |
| --- | --- | --- |
| `dj.s` | Deutsch–Jozsa, oracle `f(x) = x`; the listing of *Syntax* | `t`: safe, `(1,-1)` |
| `copy-input.s` | copies its input into a temporary and forgets the input; the listing of *Statics* | `x`: unsafe |
| `c.s` | program (c) of the measurement section's two programs: copy, measure, one joint gate, drop | `t`: record 1 safe `(1,0)`, record 0 unsafe |
| `teleport.s` | teleportation; the listing of the measurement section's two programs | `m`, `a`: safe on all four records |
| `mcx-dirty.s` | the dirty `C^3X` of *Four algorithms, as programs* (`mcx3`), four Toffolis and one loan | `a`: safe, loan handed back, `B = I` |
| `mcx-dirty-x.s` | the same with one extra `X` on the loan up front | `a`: safe, `B = X` |
| `mcx-dirty-half.s` | the same with the fourth Toffoli deleted | `a`: unsafe |
| `grover.s` | one Grover iteration, compute/phase/uncompute | `t`: safe, `(1,0)` |
| `qpe.s` | phase estimation of `T`, three counting qubits | `psi`: safe, `(0,1)` |
| `simon.s` | Simon's problem on two bits | `w`: both records safe, on different levels |
| `shor.s` | order finding, `N = 15`, base 7, lift against `{7}` | `w`: record 1 safe `|7>`, record 0 unsafe |
| `superdense.s` | superdense coding of `(1,1)` | `a`: two records unreachable, two safe `(0,1)` |
| `temp-and.s` | Gidney's measured AND | `a`: both records safe, on different levels |
| `temp-general.s` | the Spooky Pebble Game's Figure 1 at `f = AND` | `a`: both records safe, `(1,0)` |
| `rus.s` | one repeat-until-success iteration, a three-level block | `t`: record 1 unsafe, record 0 safe `(0,0,1)` |
| `learns-nothing.s` | learns nothing about the input, and the drop is still unsafe | `t`: unsafe |
| `bell-block.s` | a safe drop whose certificate is not a basis state | `t`: safe, `(1,0,0,1)` |
| `bell-pair.s` | which program a context compares: a Bell pair dropped as one tuple | `(a,b)`: safe, block dimension 4, `(1,0,0,1)` |
| `bell-pair-split.s` | the same Bell pair, dropped register by register | `a`: unsafe; `b`: unsafe |

Nineteen files. Four of them — `teleport.s`, `rus.s`, `temp-and.s` and
`temp-general.s` — write a non-tail `if`, and so use the sequencing operator.
`rus.s` is outside the compiler's domain by dimension; `bell-block.s` and
`c.s` are outside it by gate; the other sixteen compile to OpenQASM 3. Three
more files, `test/fixtures/cz-loan.s`, `test/fixtures/dirty-nonbasis.s` and
`test/fixtures/dirty-nonbasis-unsafe.s`, exercise the compiler outside this corpus.
