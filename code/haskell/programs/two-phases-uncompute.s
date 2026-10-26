-- Two disjoint phase-kickback lifetimes, with each allocation undone by hand.
prog two_phases_uncompute (x : [2]) : [2] {
    new t : [2] @ |0>;
    X t; H t; CX x t;
    H t; X t;
    drop t;
    new u : [2] @ |1>;
    H u; CX x u;
    H u;
    drop u;
    return x
}
