-- A temporary allocated on a non-basis state, (|0> + |1>)/sqrt2; not a program the paper prints.
prog nonbasis_alloc (q : [2]) : [2] {
    new t : [2] @ (1/rt2,1/rt2);
    Z t;
    drop t;
    return q
}
