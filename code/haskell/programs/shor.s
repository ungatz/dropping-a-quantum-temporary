-- shor.s: order-finding core of Shor's algorithm, N = 15, a = 7, three
-- counting qubits, temporary w holding the residue mod 15.
--
-- Site: drop w (depth 1).  Expected: record 1 (block {7}): SAFE, on the
-- basis vector of level 7.  Record 0 (the complement): UNSAFE.

prog shor (c1 : [2], c2 : [2], c3 : [2]) : [2] * [2] * [2] {
    new w : [16] @ |0>;
    perm w (1 0 2 3 4 5 6 7 8 9 10 11 12 13 14 15);   -- w starts at |1>
    H c1;  H c2;  H c3;
    diag c1 w (1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1);   -- U^4, 7^4 = 1 mod 15
    perm c2 w (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 20 24 28 17 21 25 29 18 22 26 30 19 23 27 31);           -- U^2, 7^2 = 4 mod 15
    perm c3 w (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 23 30 22 29 21 28 20 27 19 26 18 25 17 24 31);           -- U, 7 mod 15
    Swap c1 c3;
    H c3;
    diag c2 c3 (1, 1, 1, -i);
    H c2;
    diag c1 c3 (1, 1, 1, -z8^3);
    diag c1 c2 (1, 1, 1, -i);
    H c1;
    s = lift[{7}] w;
    drop w;
    return (c1, c2, c3)
}
