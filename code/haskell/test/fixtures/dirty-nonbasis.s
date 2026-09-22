-- dirty-nonbasis.s: a k >= 2 qubit temporary allocated on a known state
-- that is NOT a computational basis state (not a loan: the state is
-- declared), hit with a gate pair that cancels (Swap; Swap = identity), so
-- the certificate returned at the drop is exactly the allocation ray: not a
-- basis state, but proportional to psi (c = 1).  Exercises
-- Drop.Lang.Compile.emitReclaim's proportional-to-psi clause, which emits
-- nothing at this site rather than the old "not a basis state" refusal.
--
-- Site: drop a (depth 0).  Expected: SAFE, on the non-basis line
-- (1/rt2, 1/rt2, 0, 0).

prog dirty_nonbasis (q : [2]) : [2] {
    new a : [4] @ (1/rt2, 1/rt2, 0, 0);   -- a arrives non-basis, on (|00>+|01>)/rt2
    Swap a;
    Swap a;                               -- undone: a is back on its own ray
    drop a;
    return q
}
