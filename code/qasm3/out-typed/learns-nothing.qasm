OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[3] q;
bit[1] result;

// q[0] = x

h q[2];
cx q[2], q[1];
// t dropped unsafe: stays live

result[0] = measure q[0];
