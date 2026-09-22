-- grover.s: one Grover iteration on two input qubits, an oracle temporary,
-- compute/phase/uncompute; Diff is the exact 2|s><s| - I.
--
-- Site: drop t (depth 0).  Expected: SAFE, certificate the basis line (1,0).

prog grover (x1 : [2], x2 : [2]) : [2] * [2] {
    H x1;  H x2;
    new t : [2] @ |0>;
    CCX x1 x2 t;             -- compute the mark into t
    Z t;                     -- phase
    CCX x1 x2 t;             -- uncompute
    drop t;
    Diff x1 x2;
    return (x1, x2)
}
