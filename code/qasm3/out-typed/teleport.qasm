OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[3] q;
bit[2] c;
bit[1] result;

// q[0] = b

h q[1];
h q[2];
cx q[2], q[0];
cx q[1], q[2];
h q[1];
c[0] = measure q[1];   // lift z: survived <=> c[0] == 0
c[1] = measure q[2];   // lift w: survived <=> c[1] == 0
if (c[1] == 0) {
  if (c[0] == 0) {
  } else {
    z q[0];
    U(pi, 0, -pi) q[1];
  }
} else {
  x q[0];
  if (c[0] == 0) {
    U(pi, 0, -pi) q[2];
  } else {
    z q[0];
    U(pi, 0, -pi) q[1];
    U(pi, 0, -pi) q[2];
  }
}

result[0] = measure q[0];
