-- Program (c), with V lowered to one-qubit gates and CX.
gate Sdg : [2] = diag (1, -i);
gate Tdg : [2] = diag (1, z8^7);

prog c_decomposed (q : [2]) : [2] {
    new t : [2] @ |0>;
    H q;  CX q t;
    p = lift[{0}] t;
    Sdg t; H t; Tdg t; H t; S t;
    CX q t;
    Sdg t; H t; T t; H t; S t;
    CX q t;
    CX t q;
    drop t;
    return q
}
