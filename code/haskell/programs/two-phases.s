-- Two disjoint phase-kickback lifetimes. Both temporary drops are safe.
prog two_phases (x : [2]) : [2] {
    new t : [2] @ |0>;
    X t; H t; CX x t;
    drop t;
    new u : [2] @ |1>;
    H u; CX x u;
    drop u;
    return x
}
