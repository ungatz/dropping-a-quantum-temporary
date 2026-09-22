OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[3] q;
bit[1] result;

// q[0] = x

h q[1];
cx q[1], q[2];
// a dropped unsafe: stays live
// b dropped unsafe: stays live

result[0] = measure q[0];
