-- superdense.s: superdense coding of (b0, b1) = (1, 1); b is the input
-- register, Alice's a is the temporary, both measured after the Bell pair.
--
-- Site: drop a (depth 2).  Expected: records 11 and 10 unreachable; records
-- 01 and 00 SAFE, certificate (0,1).

prog superdense (b : [2]) : [2] {
    new a : [2] @ |0>;
    H a;
    CX a b;                  -- the shared Bell pair
    X a;                     -- Alice encodes b1 = 1
    Z a;                     -- Alice encodes b0 = 1
    CX a b;                  -- Bob decodes
    H a;
    p0 = lift[{0}] a;
    p1 = lift[{0}] b;
    drop a;
    return b
}
