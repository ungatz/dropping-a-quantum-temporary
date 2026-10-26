-- temp-and.s: a temporary AND uncomputed by measurement, as in
-- "Halving the cost of quantum addition", Quantum 2, 74 (2018).
--
-- Site: drop a (depth 1).  Expected: record 1 (block {1}): SAFE, on the
-- basis vector of level 1.  Record 0: SAFE, on the basis vector of level 0.

prog temp_and (x : [2], y : [2]) : [2] * [2] {
    new a : [2] @ |0>;
    CCX x y a;
    H a;
    m = lift[{1}] a;
    if m { diag x y (1, 1, 1, -1); } else { }
    drop a;
    return (x, y)
}
