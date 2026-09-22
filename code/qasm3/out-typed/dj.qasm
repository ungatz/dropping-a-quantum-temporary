OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[2] q;
bit[1] result;

// q[0] = x

x q[1];
h q[1];
h q[0];
cx q[0], q[1];
h q[0];
U(pi/2, pi, 0) q[1];

result[0] = measure q[0];
