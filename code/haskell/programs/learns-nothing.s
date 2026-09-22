-- learns-nothing.s: the witness of the criterion section -- the program learns nothing
-- about its input, and the drop is still unsafe.
--
-- H puts t on |+>, then CX copies t onto a (control t, target a),
-- entangling them.  Dropping t alone: t's own reduced state is I/2 at every
-- input (both Kraus operators are proportional to a projector of trace 1/2,
-- so K_i^dagger K_i = I/2), and K_0^dagger K_1 = 0 (the two blocks are
-- orthogonal, not proportional), so the drop is UNSAFE -- t is entangled
-- with a, which is returned.  The reduced state alone (maximally mixed,
-- hence "learns nothing" about the input x) is not what the criterion
-- reads; the criterion reads whether the site map factors, and here it does
-- not.  x is untouched throughout, so the verdict does not depend on x.
--
-- Site: drop t (depth 0), the file's only one.  Expected: UNSAFE.

prog learns_nothing (x : [2]) : [2] * [2] {
    new a : [2] @ |0>;
    new t : [2] @ |0>;
    H t;                     -- t := |+>
    CX t a;                  -- entangle: a := a xor t
    drop t;
    return (x, a)
}
