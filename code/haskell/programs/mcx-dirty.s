-- mcx-dirty.s: the 3-controlled X (C3X) from four Toffolis and one borrowed
-- register, after Barenco et al. The construction is also the first case study of Su, Zhou,
-- Feng and Ying, arXiv:2409.10153.
--
-- Site: drop a (depth 0).  Expected: SAFE, the loan handed back with B = I
-- (exactly as it arrived, in whatever state that was).

prog mcx3 (q1 : [2], q2 : [2], q3 : [2], q : [2], loan a : [2]) : [2] * [2] * [2] * [2] {
    CCX q3 a q;  CCX q1 q2 a;  CCX q3 a q;  CCX q1 q2 a;
    drop a;
    return (q1, q2, q3, q)
}
