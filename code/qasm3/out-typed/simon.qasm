OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[5] q;
bit[1] c;
bit[2] result;

// q[0] = x1
// q[1] = x2

h q[0];
h q[1];
ctrl @ negctrl @ ctrl @ x q[0], q[1], q[2], q[3];
ctrl @ negctrl @ negctrl @ x q[0], q[1], q[2], q[3];
negctrl @ ctrl @ ctrl @ x q[0], q[1], q[2], q[3];
negctrl @ ctrl @ negctrl @ x q[0], q[1], q[2], q[3];
negctrl @ negctrl @ x q[2], q[3], q[4];
c[0] = measure q[4];   // lift s (block [0])
if (c[0] == 1) { x q[4]; }   // reclaim the indicator
if (c[0] == 0) {
  negctrl @ x q[2], q[3];
}

result[0] = measure q[0];
result[1] = measure q[1];
