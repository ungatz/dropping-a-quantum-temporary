-- Two Grover iterations, each with its own compute/phase/uncompute temporary.
prog grover_two_rounds (x1 : [2], x2 : [2]) : [2] * [2] {
    H x1; H x2;
    new t1 : [2] @ |0>;
    CCX x1 x2 t1;
    Z t1;
    CCX x1 x2 t1;
    drop t1;
    Diff x1 x2;
    new t2 : [2] @ |0>;
    CCX x1 x2 t2;
    Z t2;
    CCX x1 x2 t2;
    drop t2;
    Diff x1 x2;
    return (x1, x2)
}
