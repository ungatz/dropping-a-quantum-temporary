OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[3] q;
bit[1] result;

// q[0] = x

// input register a, a loan: arrives in a state this program does not know
x q[1];
h q[2];
U(pi, 0, -pi) q[1];
U(pi/2, 0, -pi) q[2];

result[0] = measure q[0];
