-- bell-block.s: a safe drop of a block of dimension 4 whose certificate is
-- not a basis state.
--
-- t : [4] is allocated at |0> and carried by one exact 4x4 unitary to
-- (|0> + |3>)/sqrt2, a Bell-like ray on the block, identity on the middle
-- two levels {1,2} (so the matrix is unitary: it is the real Hadamard on
-- the {0,3} subspace, the identity on {1,2}).  x is untouched.
--
-- Site: drop t (depth 0).  Expected: SAFE, certificate the ray
-- (1,0,0,1)/sqrt2 (any global phase); the reclaiming gate is that same
-- matrix again (it is its own inverse), not the identity.  The gate is
-- outside the emitter's table, so the file does not compile to OpenQASM 3.

prog bell_block (x : [2]) : [2] {
    new t : [4] @ |0>;
    mat t {
      1/rt2, 0, 0, 1/rt2;
      0, 1, 0, 0;
      0, 0, 1, 0;
      1/rt2, 0, 0, -1/rt2
    };
    drop t;
    return x
}
