OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[4] q;
bit[1] result;

// q[0] = x

// input register a, a loan: arrives in a state this program does not know
// input register b, a loan: arrives in a state this program does not know
swap q[1], q[2];
h q[3];
cx q[1], q[2];
ctrl @ x q[2], q[1];
cx q[1], q[2];
U(pi/2, 0, -pi) q[3];

result[0] = measure q[0];
