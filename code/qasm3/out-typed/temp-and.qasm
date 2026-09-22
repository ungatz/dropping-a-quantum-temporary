OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[3] q;
bit[1] c;
bit[2] result;

// q[0] = x
// q[1] = y

ccx q[0], q[1], q[2];
h q[2];
c[0] = measure q[2];   // lift m: survived <=> c[0] == 1
if (c[0] == 1) {
  cz q[0], q[1];
  U(pi, 0, -pi) q[2];
} else {
}

result[0] = measure q[0];
result[1] = measure q[1];
