-- rus.s: one repeat-until-success iteration, unrolled; both branches of the
-- conditional are the same code.  A three-level block on a three-level
-- input register, so the file is outside the compiler's domain.
--
-- Site: drop t (depth 1).  Expected: record 1 (block {0,1}, weight 8/9):
-- UNSAFE.  Record 0 (block {2}, weight 1/9): SAFE, certificate (0,0,1).

prog rus (x : [3]) : [3] {
    new t : [3] @ |0>;
    tilt t;
    p = lift[{0,1}] t;
    if p { READ3 x t; } else { READ3 x t; }
    drop t;
    return x
}
