-- qpe.s: phase estimation of T = diag(1, zeta_8), three counting qubits,
-- eigenstate temporary psi = |1>; phase 1/8 is exact in three bits.
--
-- Site: drop psi (depth 0).  Expected: SAFE, certificate (0,1) -- the state
-- the program put psi in, not the one it was allocated in.  The final state
-- is |001> tensor |1> exactly.

prog qpe (c1 : [2], c2 : [2], c3 : [2]) : [2] * [2] * [2] {
    new psi : [2] @ |0>;
    X psi;
    H c1;  H c2;  H c3;
    diag c1 psi (1, 1, 1, -1);
    diag c2 psi (1, 1, 1, i);
    diag c3 psi (1, 1, 1, z8);
    Swap c1 c3;
    H c3;
    diag c2 c3 (1, 1, 1, -i);
    H c2;
    diag c1 c3 (1, 1, 1, -z8^3);
    diag c1 c2 (1, 1, 1, -i);
    H c1;
    drop psi;
    return (c1, c2, c3)
}
