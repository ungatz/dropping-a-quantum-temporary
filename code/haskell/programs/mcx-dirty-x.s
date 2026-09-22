-- mcx-dirty-x.s: mcx-dirty.s with one extra X on the loan immediately after
-- it arrives, so the four Toffolis uncompute the loan back to a state that
-- differs from its arrival state by exactly that X.
--
-- Site: drop a (depth 0).  Expected: SAFE, B = X (applying X once more on
-- the way out hands the loan back exactly as it arrived).

prog mcx3_x (q1 : [2], q2 : [2], q3 : [2], q : [2], loan a : [2]) : [2] * [2] * [2] * [2] {
    X a;                     -- the block's own gate: a is flipped once, up front
    CCX q3 a q;  CCX q1 q2 a;  CCX q3 a q;  CCX q1 q2 a;
    drop a;
    return (q1, q2, q3, q)
}
