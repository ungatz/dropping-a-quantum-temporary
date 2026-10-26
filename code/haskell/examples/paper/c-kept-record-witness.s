-- The witness for program (c) of the paper (ex:three) on its kept record, as built in fig:record-witness: it drops both t and a, then returns v.
prog witness (v : [2]) : [2] {
    new t : [2] @ |0>; new a : [2] @ |0>;
    H v; CX v a;
    p = lift[{0}] a; drop a;
    drop t; return v
}
