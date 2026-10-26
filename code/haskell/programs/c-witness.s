-- The witness for program (c), keeping record p=1.
prog c_witness (q : [2]) : [2] * [2] {
    new t : [2] @ |0>;
    new a : [2] @ |0>;
    H q; CX q a;
    p = lift[{0}] a;
    drop a;
    return (t, q)
}
