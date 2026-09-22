OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[2] q;
bit[2] c;
bit[1] result;

// q[0] = b

h q[1];
cx q[1], q[0];
x q[1];
z q[1];
cx q[1], q[0];
h q[1];
c[0] = measure q[1];   // lift p0: survived <=> c[0] == 0
c[1] = measure q[0];   // lift p1: survived <=> c[1] == 0
if (c[0] == 1 && c[1] == 1) {
  U(pi, 0, -pi) q[1];
}
if (c[0] == 1 && c[1] == 0) {
  U(pi, 0, -pi) q[1];
}

result[0] = measure q[0];
