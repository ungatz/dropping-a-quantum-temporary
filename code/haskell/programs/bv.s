-- bv.s: Bernstein-Vazirani, hidden string s = 11, oracle
-- |x1 x2 t> -> |x1 x2, t + s.x> as a permutation literal.
--
-- Expected: drop t at depth 0 is ADMISSIBLE, parked on the line [|->].

vis x1:2, x2:2;
new t:2;
gate X t;
gate H t;
gate H x1;
gate H x2;
perm x1 x2 t (0 1 3 2 5 4 6 7);
gate H x1;
gate H x2;
drop t;
lift p1 = meas x1 in {0};
lift p2 = meas x2 in {0};
