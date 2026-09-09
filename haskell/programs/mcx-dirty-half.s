-- mcx-dirty-half.s: mcx-dirty.s with the fourth Toffoli deleted, so the
-- ancilla is left holding q1 AND q2.
--
-- Expected: drop a is REFUSED.

vis q1:2, q2:2, q3:2, q:2;

newdirty a:2 @ (1,0);       -- the loan: a arrives on |0>
gate CCX q3 a q;            -- Toffoli(q3, a; q)
gate CCX q1 q2 a;           -- Toffoli(q1, q2; a)
gate CCX q3 a q;            -- Toffoli(q3, a; q)
-- (the fourth Toffoli is deleted: the ancilla is not uncomputed)
drop a;                     -- hand the loan back
