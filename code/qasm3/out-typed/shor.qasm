OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
qubit[8] q;
bit[1] c;
bit[3] result;

// q[0] = c1
// q[1] = c2
// q[2] = c3

negctrl @ negctrl @ negctrl @ x q[3], q[4], q[5], q[6];
h q[0];
h q[1];
h q[2];
cx q[4], q[6];
ctrl @ ctrl @ ctrl @ ctrl @ x q[1], q[3], q[5], q[6], q[4];
cx q[4], q[6];
cx q[3], q[5];
ctrl @ ctrl @ ctrl @ ctrl @ x q[1], q[4], q[5], q[6], q[3];
cx q[3], q[5];
cx q[3], q[4];
cx q[3], q[5];
cx q[3], q[6];
ctrl @ ctrl @ ctrl @ negctrl @ x q[1], q[4], q[5], q[6], q[3];
cx q[3], q[4];
cx q[3], q[5];
cx q[3], q[6];
cx q[3], q[4];
cx q[3], q[5];
cx q[3], q[6];
ctrl @ negctrl @ ctrl @ ctrl @ x q[1], q[4], q[5], q[6], q[3];
cx q[3], q[4];
cx q[3], q[5];
cx q[3], q[6];
cx q[3], q[5];
ctrl @ negctrl @ ctrl @ negctrl @ x q[1], q[4], q[5], q[6], q[3];
cx q[3], q[5];
cx q[4], q[6];
ctrl @ negctrl @ negctrl @ ctrl @ x q[1], q[3], q[5], q[6], q[4];
cx q[4], q[6];
cx q[4], q[6];
ctrl @ ctrl @ negctrl @ ctrl @ x q[2], q[3], q[5], q[6], q[4];
cx q[4], q[6];
cx q[3], q[5];
ctrl @ ctrl @ ctrl @ negctrl @ x q[2], q[4], q[5], q[6], q[3];
cx q[3], q[5];
cx q[4], q[6];
ctrl @ negctrl @ ctrl @ ctrl @ x q[2], q[3], q[5], q[6], q[4];
cx q[4], q[6];
cx q[5], q[6];
ctrl @ ctrl @ negctrl @ negctrl @ x q[2], q[3], q[4], q[6], q[5];
cx q[5], q[6];
cx q[4], q[5];
ctrl @ ctrl @ negctrl @ negctrl @ x q[2], q[3], q[5], q[6], q[4];
cx q[4], q[5];
cx q[3], q[4];
ctrl @ negctrl @ ctrl @ negctrl @ x q[2], q[4], q[5], q[6], q[3];
cx q[3], q[4];
cx q[3], q[6];
ctrl @ ctrl @ negctrl @ negctrl @ x q[2], q[4], q[5], q[6], q[3];
cx q[3], q[6];
cx q[5], q[6];
ctrl @ negctrl @ ctrl @ negctrl @ x q[2], q[3], q[4], q[6], q[5];
cx q[5], q[6];
cx q[4], q[5];
ctrl @ negctrl @ negctrl @ ctrl @ x q[2], q[3], q[5], q[6], q[4];
cx q[4], q[5];
swap q[0], q[2];
h q[2];
cp(-pi/2) q[1], q[2];
h q[1];
cp(-pi/4) q[0], q[2];
cp(-pi/2) q[0], q[1];
h q[0];
negctrl @ ctrl @ ctrl @ ctrl @ x q[3], q[4], q[5], q[6], q[7];
c[0] = measure q[7];   // lift s (block [7])
if (c[0] == 1) { x q[7]; }   // reclaim the indicator
// w dropped unsafe on record [("s",0)]: stays live
if (c[0] == 1) {
  cx q[4], q[5];
  cx q[4], q[6];
  negctrl @ negctrl @ negctrl @ x q[3], q[5], q[6], q[4];
  cx q[4], q[5];
  cx q[4], q[6];
}

result[0] = measure q[0];
result[1] = measure q[1];
result[2] = measure q[2];
