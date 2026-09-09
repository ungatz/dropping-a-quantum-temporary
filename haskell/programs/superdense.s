-- superdense.s: superdense coding of (b0, b1) = (1, 1); b is visible,
-- Alice's a is the temporary, both measured after the Bell pair.
--
-- Expected: drop a is ADMISSIBLE on every reachable trace.

vis b:2;

new a:2;
gate H a;
gate CX a b;            -- the shared Bell pair
gate X a;               -- Alice encodes b1 = 1
gate Z a;               -- Alice encodes b0 = 1
gate CX a b;            -- Bob decodes
gate H a;
lift p0 = meas a in {0};
lift p1 = meas b in {0};
drop a;
