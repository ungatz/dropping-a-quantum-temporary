-- grover.s: one Grover iteration on two visible qubits, oracle ancilla,
-- compute/phase/uncompute; Diff is the exact 2|s><s| - I.
--
-- Expected: drop t at depth 0 is ADMISSIBLE, parked on the basis line [|0>].

vis x1:2, x2:2;

gate H x1;
gate H x2;
new t:2;
gate CCX x1 x2 t;       -- compute the mark into t
gate Z t;               -- phase
gate CCX x1 x2 t;       -- uncompute
drop t;
gate Diff x1 x2;
