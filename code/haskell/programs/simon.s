-- simon.s: Simon's problem on two bits, hidden string s = 11, two-to-one
-- oracle f(00) = f(11) = 0, f(01) = f(10) = 1 as a permutation on w.
--
-- Site: drop w (depth 1).  Expected: record 1 (block {0}): SAFE, on the
-- basis vector of level 0.  Record 0: SAFE, on the basis vector of level 1.

prog simon (x1 : [2], x2 : [2]) : [2] * [2] {
    new w : [4] @ |0>;
    H x1;  H x2;
    perm x1 x2 w (0 1 2 3 5 4 7 6 9 8 11 10 12 13 14 15);
    s = lift[{0}] w;
    drop w;
    return (x1, x2)
}
