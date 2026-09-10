-- tilt.s: the program the boundary result is proved with; tilt|0> =
-- (2/3, 2/3, 1/3) has a foot in the measured block {0,1} and a foot on |2>.
--
-- Expected: selection {0,1}, weight 8/9, is INADMISSIBLE.
-- Expected: selection {2}, weight 1/9, is ADMISSIBLE.

vis x:3;
new t:3;
gate tilt t;
lift p = meas t in {0,1};
gate READ3 x t;
drop t;
