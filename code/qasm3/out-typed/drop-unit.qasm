OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[1] q;
bit[1] result;

// q[0] = x

// drop (): nothing to reclaim

result[0] = measure q[0];
