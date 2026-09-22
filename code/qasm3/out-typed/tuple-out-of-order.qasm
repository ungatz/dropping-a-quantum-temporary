OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[3] q;
bit[1] result;

// q[0] = x

x q[1];
x q[1];
x q[2];
cx q[2], q[1];
ctrl @ x q[1], q[2];
cx q[2], q[1];

result[0] = measure q[0];
