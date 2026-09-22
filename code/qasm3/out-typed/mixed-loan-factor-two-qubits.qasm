OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[4] q;
bit[1] result;

// q[0] = x

// input register a, a loan: arrives in a state this program does not know
// input register b, a loan: arrives in a state this program does not know
h q[1];
h q[3];
// reclaim of a,b,t not emitted: the loan factor of B = B' (x) g is on more than one qubit

result[0] = measure q[0];
