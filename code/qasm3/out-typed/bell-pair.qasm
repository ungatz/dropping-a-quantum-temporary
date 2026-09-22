OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[3] q;
bit[1] result;

// q[0] = x

h q[1];
cx q[1], q[2];
ctrl @ x q[1], q[2];
U(pi/4, 0, -pi) q[1];
negctrl @ z q[2], q[1];
U(-pi/4, pi, 0) q[1];
ctrl @ x q[1], q[2];

result[0] = measure q[0];
