-- The program channelSafe of the paper (prop:channel, drawn in fig:summed-channel).
prog channelSafe (q : [2]) : [2] {
    new t : [2] @ |0>; H t;
    diag t q (1,1,1,-1);
    p = lift[{0}] t;
    drop t; return q
}
