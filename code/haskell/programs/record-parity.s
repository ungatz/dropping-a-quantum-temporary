-- Two readings of the temporary give the record p q. H before each lift
-- makes both readings possible. Each true bit applies CX to the temporary.
--
-- Site: drop t (depth 2). Records 11 and 00: SAFE, with t in |0> and |1>.
-- Records 01 and 10: UNSAFE. Neither bit alone decides the drop.

prog record_parity (x : [2]) : [2] {
    new t : [2] @ |0>;
    H t;
    p = lift[{0}] t;
    H t;
    q = lift[{0}] t;
    if p { CX x t; } else { }
    if q { CX x t; } else { }
    drop t;
    return x
}
