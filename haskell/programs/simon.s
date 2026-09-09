-- simon.s: Simon's problem on two bits, hidden string s = 11, two-to-one
-- oracle f(00) = f(11) = 0, f(01) = f(10) = 1 as a permutation on w.
--
-- Expected: drop w on the block {0} is ADMISSIBLE, parked on the basis
-- vector of level 0.
-- Expected: drop w on the complement of {0} is ADMISSIBLE, parked on the
-- basis vector of level 1.

vis x1:2, x2:2;
new w:4;
gate H x1;
gate H x2;
perm x1 x2 w (0 1 2 3 5 4 7 6 9 8 11 10 12 13 14 15);
lift s = meas w in {0};
drop w;
