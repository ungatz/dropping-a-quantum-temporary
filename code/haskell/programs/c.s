-- c.s: program (c). It allocates a temporary, applies H to the visible
-- register, copies it into the temporary, measures whether the temporary
-- landed on |0>, applies V, and drops. The declaration below specifies V.
--
-- V is the real orthogonal gate fixing |00>, sending |10> to |11> and |01>,
-- |11> to (|01> -+ |10>)/sqrt2, the temporary written first.
--
-- Site: drop t (depth 1).  Expected: record 1 (t landed on |0>): SAFE,
-- certificate (1,0).  Record 0: UNSAFE.

gate V : [2] * [2] = mat {
  1, 0,      0, 0;
  0, 1/rt2,  0, 1/rt2;
  0, -1/rt2, 0, 1/rt2;
  0, 0,      1, 0
};

prog c (q : [2]) : [2] {
    new t : [2] @ |0>;
    H q;  CX q t;            -- copy q into t
    p = lift[{0}] t;         -- did t land on |0>?
    V t q;                   -- whatever p said
    drop t;
    return q
}
