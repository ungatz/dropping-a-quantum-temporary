-- Program (a) of the paper, "superpose, then drop" (ex:three).
prog a (v : [2]) : [2] {
    new t : [2] @ |0>;
    H t;
    drop t;
    return v
}
