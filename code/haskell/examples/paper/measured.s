-- The program measured of the paper (app:deferral).
prog measured (q : [2]) : [2] {
    new t : [2] @ |0>; H t;
    p = lift[{0}] t;
    drop t;
    return q
}
