-- dj.s: Deutsch-Jozsa on one visible qubit, |-> ancilla, oracle f(x) = x
-- as CX with control x and target t.
--
-- Expected: drop t at depth 0 is ADMISSIBLE, parked on the line [|->].

vis x:2;

new t:2;
gate X t;               -- t := |1>
gate H t;               -- t := |->
gate H x;
gate CX x t;            -- the oracle for f(x) = x
gate H x;
drop t;
lift r = meas x in {0};
