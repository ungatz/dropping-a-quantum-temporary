-- The program twice of the paper (app:meas-tree).
prog twice (q : [2]) : [2] {
    new t : [2] @ |0>;
    H t;
    p = lift[{0}] t;
    if p { } else { X q; }
    r = lift[{0}] t;
    drop t; return q
}
