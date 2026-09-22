OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[3] q;
bit[1] result;

// q[0] = x

// input register a, a loan: arrives in a state this program does not know
h q[2];
cx q[2], q[1];
// reclaim of a,t not emitted: B : H_loan -> H_block entangles the loans with the temporaries beside them

result[0] = measure q[0];
