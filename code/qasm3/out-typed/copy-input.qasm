OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[2] q;
bit[1] result;

// q[0] = x

cx q[0], q[1];
// x dropped unsafe: stays live

result[0] = measure q[0];
