-- teleport.s: teleportation of |+> = H|0> onto visible wire b; two lifts,
-- classically controlled corrections, two drops.
--
-- Expected: drops m and a at depth 2 are ADMISSIBLE at all four selections,
-- parked on definite basis lines.

vis b:2;

new m:2;
gate H m;               -- the message |+>
new a:2;
gate H a;
gate CX a b;            -- Bell pair on (a, b)
gate CX m a;
gate H m;
lift z = meas m in {0};
lift w = meas a in {0};
if w { } else { gate X b; }
if z { } else { gate Z b; }
drop m;
drop a;
