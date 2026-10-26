-- teleport.s: teleportation of |+> = H|0> onto the input register b, which the caller
-- supplies in |0>; two lifts,
-- classically controlled corrections, two drops.  Token-identical to the
-- listing in the paper's two programs of the measurement section (sec:meas:programs).
--
-- Sites: drop m and drop a (depth 2).  Expected: SAFE at all four records,
-- each on a definite basis line -- (1,0) or (0,1) by record.

prog teleport (b : [2]) : [2] {
    new m : [2] @ |0>;  H m;
    new a : [2] @ |0>;  H a;  CX a b;
    CX m a;  H m;
    z = lift[{0}] m;  w = lift[{0}] a;
    if w {} else { X b; }
    if z {} else { Z b; }
    drop m;  drop a;
    return b
}
