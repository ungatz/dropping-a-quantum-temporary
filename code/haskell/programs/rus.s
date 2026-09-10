-- rus.s: one repeat-until-success iteration, unrolled; both branches of the
-- conditional are the same code.
--
-- Expected: drop t at depth 1, selection 1 (block {0,1}, weight 8/9):
-- INADMISSIBLE.
-- Expected: drop t at depth 1, selection 0 (block {2}, weight 1/9):
-- ADMISSIBLE, on the line (0, 0, 1).  The prefix parks t on (1, 1, 1/2);
-- selecting {2} is what leaves it on the basis line |2>.

vis x:3;

new t:3;
gate tilt t;
lift p = meas t in {0,1};
if p { gate READ3 x t; } else { gate READ3 x t; }
drop t;
