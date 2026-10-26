-- The loan and temporary example of the paper (fig:loan-return); the abstract
-- prints the same program with the loan named l.
prog mixed (loan a : [2]) : 1 {
    new t : [2] @ |0>;
    H t; X a;
    drop (a,t); return ()
}
