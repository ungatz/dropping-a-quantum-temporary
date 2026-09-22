OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[5] q;
bit[4] result;

// q[0] = q1
// q[1] = q2
// q[2] = q3
// q[3] = q

// input register a, a loan: arrives in a state this program does not know
x q[4];
ccx q[2], q[4], q[3];
ccx q[0], q[1], q[4];
ccx q[2], q[4], q[3];
ccx q[0], q[1], q[4];
U(pi, 0, -pi) q[4];

result[0] = measure q[0];
result[1] = measure q[1];
result[2] = measure q[2];
result[3] = measure q[3];
