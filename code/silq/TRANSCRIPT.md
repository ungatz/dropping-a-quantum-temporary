# Silq transcripts

What Silq says about each program in `programs/`, taken verbatim from the
recorded runs.  Apart from the two group headings, only commands and tool
output appear below.  `run_silq.sh` reproduces the type-check column against
any build.

Two binaries were used.  Each block says which, except the 20-seed sweep at
the end, whose attribution is inferred and is marked there.  The programs
`e1` to `e11` were run against silq built from commit `a47d974`; the programs
`r1` to `r8d` were run against silq built from commit `5417dce`.

Every program in `programs/` has a recorded run; nothing is missing, and
nothing below is reconstructed.  One block carries an edit, and it is the
only one: `r4-local-borrow-attempt.slq` was recorded under an earlier file
name, so the file name in its command and in its diagnostic follows the
current name of the program.  Nothing else in that block is changed, and the
line and column it reports still point at the same line of the same file.

The seeds a block was run at are named in its label, and Silq prints the seed
itself at the head of each run's output.  The two seed sweeps are the
exception: they are summarised rather than reproduced seed by seed.

Silq spells the boolean type `B` and `𝔹`, and both spellings occur in
`programs/`.  They are the same type: `e9-park-witness.slq` writes `𝔹` and
`r4d-dirty-witness-attempt.slq` writes `B`, and both draw the same
diagnostic.

---

## Programs e1 to e11 -- silq built from commit a47d974

Each was type-checked with `silq <file>`, and the blocks carry `run_silq.sh`'s
own two-space indent.  The heading for this group:

```
# silq transcript
# binary: silq built from commit a47d974
```

### e1-lifted-baseline.slq

```
=== e1-lifted-baseline.slq
  TYPECHECKS (no diagnostic)
```

### e2-nonqfree-producer.slq

```
=== e2-nonqfree-producer.slq
  e2-nonqfree-producer.slq:6:11: error: cannot synthesize forget expression for `y`
  	forget(y);
  	       ^
```

### e3-HH-is-identity.slq

```
=== e3-HH-is-identity.slq
  e3-HH-is-identity.slq:10:11: error: cannot synthesize forget expression for `z`
  	forget(z);
  	       ^
```

### e4-HH-with-hint.slq

```
=== e4-HH-with-hint.slq
  TYPECHECKS (no diagnostic)
```

### e5-HH-run.slq

```
=== e5-HH-run.slq
  TYPECHECKS (no diagnostic)
```

### e6-entangled-forget.slq

```
=== e6-entangled-forget.slq
  TYPECHECKS (no diagnostic)
```

### e7-dephased.slq

```
=== e7-dephased.slq
  TYPECHECKS (no diagnostic)
```

### e8-spread-and-park.slq

```
=== e8-spread-and-park.slq
  e8-spread-and-park.slq:7:11: error: cannot synthesize forget expression for `t`
  	forget(t);
  	       ^
```

### e9-park-witness.slq

```
=== e9-park-witness.slq
  e9-park-witness.slq:7:13: error: quantum control expression must be `lifted`
  	forget(t=H(0:𝔹));
  	         ^─────
```

### e10-spread-and-read-auto.slq

```
=== e10-spread-and-read-auto.slq
  e10-spread-and-read-auto.slq:10:11: error: cannot synthesize forget expression for `t`
  	forget(t);
  	       ^
```

### e11-measure-then-read.slq

```
=== e11-measure-then-read.slq
  e11-measure-then-read.slq:10:7: error: undefined identifier t
  	if t { x := X(x); }   // use t AFTER measuring it
  	   ^
  e11-measure-then-read.slq:8:16: note: previous declaration `t: 𝔹` consumed here
  	p := measure(t);
  	            ^──
  e11-measure-then-read.slq:11:11: error: undefined identifier t
  	forget(t);
  	       ^
  e11-measure-then-read.slq:8:16: note: previous declaration `t: 𝔹` consumed here
  	p := measure(t);
  	            ^──
```

---

## Programs r1 to r8d -- silq built from commit 5417dce

### r1-deutsch-jozsa.slq

Type check.

```
~/lib/silq/silq r1-deutsch-jozsa.slq
```

```
r1-deutsch-jozsa.slq:12:11: error: cannot synthesize forget expression for `y`
	forget(y);                // THE DROP UNDER TEST: y is |->, not |0>
	       ^
exit status: 1
```

### r1c1-dj-measure-control.slq

Type check.

```
~/lib/silq/silq r1c1-dj-measure-control.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1.

```
~/lib/silq/silq r1c1-dj-measure-control.slq --run
```

```
--seed=1:
0
exit status: 0
```

### r1c2-dj-cleanup-control.slq

Type check.

```
~/lib/silq/silq r1c2-dj-cleanup-control.slq
```

```
r1c2-dj-cleanup-control.slq:15:11: error: cannot synthesize forget expression for `y`
	forget(y);
	       ^
exit status: 1
```

### r1c3-dj-cleanup-hint-control.slq

Type check.

```
~/lib/silq/silq r1c3-dj-cleanup-hint-control.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1.

```
~/lib/silq/silq r1c3-dj-cleanup-hint-control.slq --run
```

```
--seed=1:
0
exit status: 0
```

### r1c4-dj-implicit-drop.slq

Type check.

```
~/lib/silq/silq r1c4-dj-implicit-drop.slq
```

```
r1c4-dj-implicit-drop.slq:12:4: error: variable `y` is not consumed (perhaps return it)
	y xor= f(x);              // phase kickback: (-1)^f(x) onto x
	^──────────
r1c4-dj-implicit-drop.slq:15:4: note: at function return
	return measure(x);
	^────────────────
exit status: 1
```

### r2-bernstein-vazirani.slq

Type check.

```
~/lib/silq/silq r2-bernstein-vazirani.slq
```

```
r2-bernstein-vazirani.slq:10:11: error: cannot synthesize forget expression for `y`
	forget(y);                                    // THE DROP UNDER TEST
	       ^
exit status: 1
```

### r2c1-bv-measure-control.slq

Type check.

```
~/lib/silq/silq r2c1-bv-measure-control.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1.

```
~/lib/silq/silq r2c1-bv-measure-control.slq --run
```

```
--seed=1:
5
exit status: 0
```

### r2c2-bv-cleanup-control.slq

Type check.

```
~/lib/silq/silq r2c2-bv-cleanup-control.slq
```

```
r2c2-bv-cleanup-control.slq:13:11: error: cannot synthesize forget expression for `y`
	forget(y);
	       ^
exit status: 1
```

### r3-grover-compute-uncompute.slq

Type check.

```
~/lib/silq/silq r3-grover-compute-uncompute.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1 2 3.

```
~/lib/silq/silq r3-grover-compute-uncompute.slq --run
```

```
--seed=1:
11
exit status: 0
--seed=2:
11
exit status: 0
--seed=3:
11
exit status: 0
```

### r3c1-grover-implicit.slq

Type check.

```
~/lib/silq/silq r3c1-grover-implicit.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1 2 3.

```
~/lib/silq/silq r3c1-grover-implicit.slq --run
```

```
--seed=1:
11
exit status: 0
--seed=2:
11
exit status: 0
--seed=3:
11
exit status: 0
```

### r4-c3x-dirty-ancilla.slq

Type check.

```
~/lib/silq/silq r4-c3x-dirty-ancilla.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1 to 10.

```
~/lib/silq/silq r4-c3x-dirty-ancilla.slq --run
```

```
--seed=1:
(1,0,1,1,1)
exit status: 0
--seed=2:
(1,0,1,1,1)
exit status: 0
--seed=3:
(1,0,1,1,1)
exit status: 0
--seed=4:
(1,0,1,1,1)
exit status: 0
--seed=5:
(1,0,1,1,1)
exit status: 0
--seed=6:
(1,0,1,1,1)
exit status: 0
--seed=7:
(1,0,1,1,1)
exit status: 0
--seed=8:
(1,0,1,1,1)
exit status: 0
--seed=9:
(1,0,1,1,1)
exit status: 0
--seed=10:
(1,0,1,1,1)
exit status: 0
```

### r4-local-borrow-attempt.slq

Type check.

```
~/lib/silq/silq r4-local-borrow-attempt.slq
```

```
r4-local-borrow-attempt.slq:12:11: error: cannot synthesize forget expression for `d`
	forget(d);                // THE RELEASE -- d is back in its lent state
	       ^
exit status: 1
```

### r4c-c3x-dirty-unchecked.slq

Type check.

```
~/lib/silq/silq r4c-c3x-dirty-unchecked.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1 to 10.

```
~/lib/silq/silq r4c-c3x-dirty-unchecked.slq --run
```

```
--seed=1:
(1,1)
exit status: 0
--seed=2:
(1,0)
exit status: 0
--seed=3:
(1,0)
exit status: 0
--seed=4:
(1,1)
exit status: 0
--seed=5:
(1,0)
exit status: 0
--seed=6:
(1,1)
exit status: 0
--seed=7:
(1,0)
exit status: 0
--seed=8:
(1,0)
exit status: 0
--seed=9:
(1,0)
exit status: 0
--seed=10:
(1,0)
exit status: 0
```

### r4d-dirty-witness-attempt.slq

Type check.

```
~/lib/silq/silq r4d-dirty-witness-attempt.slq
```

```
r4d-dirty-witness-attempt.slq:6:15: error: quantum control expression must be `lifted`
	forget(d = H(0:B));
	           ^─────
exit status: 1
```

### r5-phase-estimation.slq

Type check.

```
~/lib/silq/silq r5-phase-estimation.slq
```

```
r5-phase-estimation.slq:25:11: error: cannot synthesize forget expression for `u`
	forget(u);        // THE DROP UNDER TEST: u is still the eigenstate |->
	       ^
exit status: 1
```

### r5c1-pe-measure-control.slq

Type check.

```
~/lib/silq/silq r5c1-pe-measure-control.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1 2 3.

```
~/lib/silq/silq r5c1-pe-measure-control.slq --run
```

```
--seed=1:
0
exit status: 0
--seed=2:
0
exit status: 0
--seed=3:
4
exit status: 0
```

### r5c2-pe-qfree-eigenstate-control.slq

Type check.

```
~/lib/silq/silq r5c2-pe-qfree-eigenstate-control.slq
```

```
r5c2-pe-qfree-eigenstate-control.slq:23:11: error: cannot synthesize forget expression for `u`
	forget(u);        // THE SAME DROP, on a qfree-produced eigenstate
	       ^
exit status: 1
```

### r5c3-qfree-baseline.slq

Type check.

```
~/lib/silq/silq r5c3-qfree-baseline.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1.

```
~/lib/silq/silq r5c3-qfree-baseline.slq --run
```

```
--seed=1:
 √1.0000000 · |0⟩
exit status: 0
```

### r6-superdense-coding.slq

Type check.

```
~/lib/silq/silq r6-superdense-coding.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1 2 3.

```
~/lib/silq/silq r6-superdense-coding.slq --run
```

```
--seed=1:
(1,0)
exit status: 0
--seed=2:
(1,0)
exit status: 0
--seed=3:
(1,0)
exit status: 0
```

### r6b-superdense-drop.slq

Type check.

```
~/lib/silq/silq r6b-superdense-drop.slq
```

```
r6b-superdense-drop.slq:12:11: error: cannot synthesize forget expression for `b`
	forget(b);            // THE DROP UNDER TEST
	       ^
exit status: 1
```

### r6c-superdense-drop-hint.slq

Type check.

```
~/lib/silq/silq r6c-superdense-drop-hint.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1 2 3.

```
~/lib/silq/silq r6c-superdense-drop-hint.slq --run
```

```
--seed=1:
1
exit status: 0
--seed=2:
1
exit status: 0
--seed=3:
1
exit status: 0
```

### r7-teleportation.slq

Type check.

```
~/lib/silq/silq r7-teleportation.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1 to 8.

```
~/lib/silq/silq r7-teleportation.slq --run
```

```
--seed=1:
0
exit status: 0
--seed=2:
0
exit status: 0
--seed=3:
0
exit status: 0
--seed=4:
0
exit status: 0
--seed=5:
0
exit status: 0
--seed=6:
0
exit status: 0
--seed=7:
0
exit status: 0
--seed=8:
0
exit status: 0
```

### r7b-teleport-state.slq

Type check.

```
~/lib/silq/silq r7b-teleport-state.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1 2 3 4.

```
~/lib/silq/silq r7b-teleport-state.slq --run
```

```
--seed=1:
 √0.5000000∠0.0000000 · |0⟩
+√0.5000000∠1.5707963 · |1⟩
exit status: 0
--seed=2:
 √0.5000000∠0.0000000 · |0⟩
+√0.5000000∠1.5707963 · |1⟩
exit status: 0
--seed=3:
 √0.5000000∠0.0000000 · |0⟩
+√0.5000000∠1.5707963 · |1⟩
exit status: 0
--seed=4:
 √0.5000000∠0.0000000 · |0⟩
+√0.5000000∠1.5707963 · |1⟩
exit status: 0
```

### r7c-measure-consumes.slq

Type check.

```
~/lib/silq/silq r7c-measure-consumes.slq
```

```
r7c-measure-consumes.slq:8:7: error: undefined identifier t
	if t { x := X(x); }   // ATTEMPT: keep using t after measuring it
	   ^
r7c-measure-consumes.slq:6:16: note: previous declaration `t: 𝔹` consumed here
	p := measure(t);   // measure consumes t
	            ^──
r7c-measure-consumes.slq:9:11: error: undefined identifier t
	forget(t);
	       ^
r7c-measure-consumes.slq:6:16: note: previous declaration `t: 𝔹` consumed here
	p := measure(t);   // measure consumes t
	            ^──
exit status: 1
```

### r8a-repeat-until-syntax.slq

Type check.

```
~/lib/silq/silq r8a-repeat-until-syntax.slq
```

```
r8a-repeat-until-syntax.slq:5:11: error: found "{" when expecting expression
	repeat { (q0, q1) := (H(0:B), H(0:B)); }
	       ^
r8a-repeat-until-syntax.slq:5:13: error: found "(" when expecting "{"
	repeat { (q0, q1) := (H(0:B), H(0:B)); }
	         ^
r8a-repeat-until-syntax.slq:7:4: error: found "else" when expecting expression
	else { measure(q0, q1) }
	^───
r8a-repeat-until-syntax.slq:7:8: error: expected ";"
	else { measure(q0, q1) }
	    ^
r8a-repeat-until-syntax.slq:7:9: error: found "{" when expecting expression
	else { measure(q0, q1) }
	     ^
r8a-repeat-until-syntax.slq:9:0: error: found "}" when expecting expression
}
^
r8a-repeat-until-syntax.slq:9:1: error: expected ";"
}
 ^
exit status: 1
```

### r8b-rus-while.slq

Type check.

```
~/lib/silq/silq r8b-rus-while.slq
```

```
(no output)
exit status: 0
```

Run, seeds 1 to 5.

```
~/lib/silq/silq r8b-rus-while.slq --run
```

```
--seed=1:
 √0.3333333 · |0⟩
+√0.3333333 · |1⟩
+√0.3333333 · |2⟩
exit status: 0
--seed=2:
 √0.3333333 · |0⟩
+√0.3333333 · |1⟩
+√0.3333333 · |2⟩
exit status: 0
--seed=3:
 √0.3333333 · |0⟩
+√0.3333333 · |1⟩
+√0.3333333 · |2⟩
exit status: 0
--seed=4:
 √0.3333333 · |0⟩
+√0.3333333 · |1⟩
+√0.3333333 · |2⟩
exit status: 0
--seed=5:
 √0.3333333 · |0⟩
+√0.3333333 · |1⟩
+√0.3333333 · |2⟩
exit status: 0
```

### r8c-rus-auto-forget-control.slq

Type check.

```
~/lib/silq/silq r8c-rus-auto-forget-control.slq
```

```
r8c-rus-auto-forget-control.slq:16:15: error: cannot synthesize forget expression for `q`
		forget(q);   // CONTROL: automatic uncomputation, no witness
		       ^
exit status: 1
```

### r8d-rus-wrong-witness.slq

Type check.

```
~/lib/silq/silq r8d-rus-wrong-witness.slq
```

```
(no output)
exit status: 0
```

Run, the sweep over seeds 1 to 40.  The block below is one failing run of the
forty, kept for the shape of the diagnostic; the seeds that fail are listed at
the end of this file.

```
for s in $(seq 1 40); do ~/lib/silq/silq r8d-rus-wrong-witness.slq --run --seed=$s; done
```

```
r8d-rus-wrong-witness.slq:16:8: error: bad forget
		forget(q = 0);   // WRONG witness: q is |3> here, not |0>
		^────────────
r8d-rus-wrong-witness.slq:25:20: note: called from here
def main() { return prepare3(); }
                    ^─────────
exit status: 1
```

---

## The 20-seed sweep of r8d-rus-wrong-witness.slq

Recorded separately from the sweep above, and over 20 seeds rather than 40.
Its source states no commit for the binary; it says only that the build is
the one the `r1` to `r8d` runs used, which is `5417dce`.  That attribution
is therefore inferred and not stated.

```
$ ~/lib/silq/silq r8d-rus-wrong-witness.slq --run --seed=1 .. 20
```

```
seeds 4, 6, 8, 10, 13, 15 : error: bad forget   (6 of 20; expected branch rate 1/4)
the other 14 seeds        : √0.3333333 · |0⟩ +√0.3333333 · |1⟩ +√0.3333333 · |2⟩
```

The six failing seeds are exactly the failing seeds of the 40-seed sweep
that lie in 1 to 20; that sweep fails on seeds 4, 6, 8, 10, 13, 15, 24, 25,
29, 32 and 37.  No per-seed output is recorded for the seeds that succeed,
in either sweep.
