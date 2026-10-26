-- Program (b) of the paper, "superpose, then read" (ex:three).
prog b (v : [2]) : [2] {
    new t : [2] @ |0>;
    H t;
    CX t v;
    drop t;
    return v
}
