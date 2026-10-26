-- The program deferred of the paper (app:deferral).
prog deferred (q : [2]) : [2] {
    new t : [2] @ |0>; H t;
    new a : [2] @ |1>; CX t a;
    drop t;
    p = lift[{1}] a;
    drop a; return q
}
