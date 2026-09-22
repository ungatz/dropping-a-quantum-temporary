-- dj.s: Deutsch-Jozsa on one input qubit, |-> temporary, oracle f(x) = x as
-- CX with control x and target t.  Token-identical to the listing in
-- the syntax subsection of the paper.
--
-- Site: drop t (depth 0).  Expected: SAFE, certificate the line (1,-1).

prog dj (x : [2]) : [2] {
    new t : [2] @ |0>;
    X t;  H t;               -- t := |->
    H x;  CX x t;  H x;      -- the oracle
    drop t;
    return x
}
