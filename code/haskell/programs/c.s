-- Program (c), with the data register named q. After H on q, it copies q
-- into a temporary, measures the temporary, applies V, and drops it.
-- With the temporary first, V fixes |00>, sends |10> to |11>,
-- and sends |01> and |11> to (|01> - |10>)/sqrt2 and
-- (|01> + |10>)/sqrt2, respectively.
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
