-- mcx-dirty-plus.s: mcx-dirty.s with the loan on |+> instead of |0>.
--
-- Expected: drop a is ADMISSIBLE, parked on |+>, the loan's own ray.

vis q1:2, q2:2, q3:2, q:2;

newdirty a:2 @ (1/rt2,1/rt2);   -- the loan: a arrives on |+>
gate CCX q3 a q;            -- Toffoli(q3, a; q)
gate CCX q1 q2 a;           -- Toffoli(q1, q2; a)
gate CCX q3 a q;            -- Toffoli(q3, a; q)
gate CCX q1 q2 a;           -- Toffoli(q1, q2; a)
drop a;                     -- hand the loan back
