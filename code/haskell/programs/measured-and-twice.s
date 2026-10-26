-- Two measured-AND temporaries in sequence; each drop is safe on both records.
prog measured_and_twice (x : [2], y : [2]) : [2] * [2] {
    new a : [2] @ |0>;
    CCX x y a;
    H a;
    m1 = lift[{1}] a;
    if m1 { diag x y (1, 1, 1, -1); } else { }
    drop a;
    new b : [2] @ |0>;
    CCX x y b;
    H b;
    m2 = lift[{1}] b;
    if m2 { diag x y (1, 1, 1, -1); } else { }
    drop b;
    return (x, y)
}
