-- qpe.s: phase estimation of T = diag(1, zeta_8), three counting qubits,
-- eigenstate temporary psi = |1>; phase 1/8 is exact in three bits.
--
-- Expected: drop psi at depth 0 is ADMISSIBLE, parked on [|1>]; final state
-- is |001> tensor |1> exactly.

vis c1:2, c2:2, c3:2;
new psi:2;
gate X psi;
gate H c1;
gate H c2;
gate H c3;
diag c1 psi (1, 1, 1, -1);
diag c2 psi (1, 1, 1, i);
diag c3 psi (1, 1, 1, z8);
gate Swap c1 c3;
gate H c3;
diag c2 c3 (1, 1, 1, -i);
gate H c2;
diag c1 c3 (1, 1, 1, -z8^3);
diag c1 c2 (1, 1, 1, -i);
gate H c1;
drop psi;
