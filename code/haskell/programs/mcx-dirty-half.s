-- mcx-dirty-half.s: mcx-dirty.s with the fourth Toffoli deleted, so the
-- loan is left holding q1 AND q2.
--
-- Site: drop a (depth 0).  Expected: UNSAFE (the loan is not handed back).

prog mcx3_half (q1 : [2], q2 : [2], q3 : [2], q : [2], loan a : [2]) : [2] * [2] * [2] * [2] {
    CCX q3 a q;  CCX q1 q2 a;  CCX q3 a q;
    -- (the fourth Toffoli is deleted: the loan is not uncomputed)
    drop a;
    return (q1, q2, q3, q)
}
