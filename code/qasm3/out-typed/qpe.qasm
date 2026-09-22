OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[4] q;
bit[3] result;

// q[0] = c1
// q[1] = c2
// q[2] = c3

x q[3];
h q[0];
h q[1];
h q[2];
cz q[0], q[3];
cp(pi/2) q[1], q[3];
cp(pi/4) q[2], q[3];
swap q[0], q[2];
h q[2];
cp(-pi/2) q[1], q[2];
h q[1];
cp(-pi/4) q[0], q[2];
cp(-pi/2) q[0], q[1];
h q[0];
U(pi, 0, -pi) q[3];

result[0] = measure q[0];
result[1] = measure q[1];
result[2] = measure q[2];
