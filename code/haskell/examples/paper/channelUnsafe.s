-- The program channelUnsafe of the paper (prop:channel, drawn in fig:summed-channel).
prog channelUnsafe (q : [2]) : [2] {
    new t : [2] @ |0>; H t;
    p = lift[{0}] t;
    CX q t;
    drop t; return q
}
