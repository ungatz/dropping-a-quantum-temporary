-- temp-and.s: a temporary AND uncomputed by measurement, as in Gidney,
-- "Halving the cost of quantum addition", Quantum 2, 74 (2018).
--
-- Expected: drop a on the block {1} is ADMISSIBLE, parked on the basis
-- vector of level 1.
-- Expected: drop a on the complement of {1} is ADMISSIBLE, parked on the
-- basis vector of level 0.

vis x:2, y:2;
new a:2;
gate CCX x y a;
gate H a;
lift m = meas a in {1};
if m { diag x y (1, 1, 1, -1); } else { }
drop a;
