-- mcx-dirty.s: the 3-controlled X (C3X) from four Toffolis and one borrowed
-- ancilla. The construction is Gidney's; it is the first case study of Su,
-- Zhou, Feng and Ying, arXiv:2409.10153.
--
-- Expected: drop a is ADMISSIBLE, parked on the loan's own ray (1, 0).

vis q1:2, q2:2, q3:2, q:2;

newdirty a:2 @ (1,0);       -- the loan: a arrives on |0>
gate CCX q3 a q;            -- Toffoli(q3, a; q)
gate CCX q1 q2 a;           -- Toffoli(q1, q2; a)
gate CCX q3 a q;            -- Toffoli(q3, a; q)
gate CCX q1 q2 a;           -- Toffoli(q1, q2; a)
drop a;                     -- hand the loan back
