OPENQASM 3.0;
include "stdgates.inc";

// emitted by Drop.Lang.Compile, the compiler of the paper's language.
gate diff a, b { h a; h b; x a; x b; cz a, b; x a; x b; h a; h b; }   // Grover diffusion, up to global phase
qubit[3] q;
bit[2] result;

// q[0] = x1
// q[1] = x2

h q[0];
h q[1];
ccx q[0], q[1], q[2];
z q[2];
ccx q[0], q[1], q[2];
diff q[0], q[1];

result[0] = measure q[0];
result[1] = measure q[1];
