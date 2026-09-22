-- cz-loan.s: a loan hit with a controlled-Z against the input register,
-- then dropped with nothing to undo the entanglement.  CZ keeps every basis
-- label of t fixed, so a temporary would pass the old "same basis label"
-- intuition; a loan is a different question -- is there a fixed unitary B
-- on t alone that reproduces the whole joint action, whatever the loan
-- arrives on? -- and CZ is not of that form: the block/rest reshape
-- (Drop.Lang.Interp's loan criterion) fails to factor at all.
--
-- Site: drop t (depth 0).  Expected: UNSAFE.

prog cz_loan (r : [2], loan t : [2]) : [2] {
    diag t r (1, 1, 1, -1);   -- CZ on t, r
    drop t;
    return r
}
