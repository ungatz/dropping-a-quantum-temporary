-- Like dirty-nonbasis.s, allocate a known non-basis temporary; the diagonal
-- interaction with q makes the drop unsafe by correlating a with the input.
prog dirty_nonbasis_unsafe (q : [2]) : [2] {
    new a : [4] @ (1/rt2, 1/rt2, 0, 0);
    diag a q (1, 1, 1, -1, 1, 1, 1, 1);
    drop a;
    return q
}
