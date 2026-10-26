-- mcx-dirty.s: the 3-controlled X (C3X) from four Toffolis and one borrowed
-- register, after "Elementary Gates for Quantum Computation", Physical Review A 52
-- (1995).  Token-identical to the mcx3 listing in the paper's four algorithms (sec:lang:algorithms).  The
-- construction is also the first case study of "An Interpretation of Bunched Logic for
-- Reasoning about Heap-Manipulating Quantum Programs", arXiv:2409.10153.
--
-- Site: drop a (depth 0).  Expected: SAFE, the loan handed back with B = I
-- (exactly as it arrived, in whatever state that was).

prog mcx3 (q1 : [2], q2 : [2], q3 : [2], q : [2], loan a : [2]) : [2] * [2] * [2] * [2] {
    CCX q3 a q;  CCX q1 q2 a;  CCX q3 a q;  CCX q1 q2 a;
    drop a;
    return (q1, q2, q3, q)
}
