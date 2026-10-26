-- bell-pair.s: which program a context compares.  Two temporaries are
-- allocated, entangled into a Bell pair, and dropped TOGETHER as one tuple:
-- the composite drop is one site of block dimension 4, and it is SAFE, on
-- the fixed ray (|00> + |11>)/sqrt2.  bell-pair-split.s is the same
-- circuit with the two registers dropped one at a time instead, and every
-- drop there is UNSAFE.  The two files are the same program compared by
-- two different contexts, in the Remark's sense: safety is a property of
-- the drop, not of the temporaries alone.
--
-- H puts a on |+>, then CX entangles b to it, so (a, b) leaves on
-- (|00> + |11>)/sqrt2.  The reclaiming gate for this block is the
-- two-qubit reflection through |00> - (|00> + |11>)/sqrt2, and the emitter
-- writes it (Drop.Lang.Compile.Emit.emitTwoSupportReflectionOps, the two-support
-- shortcut of the general clause): cx, a rotation on a, negctrl @ z, the
-- rotation's inverse, cx -- five lines, checked by qasm3/compile_check.py
-- against the machine's state.
--
-- Site: drop (a, b) (depth 0), the file's only one.  Expected: SAFE, block
-- dimension 4, certificate the ray (1,0,0,1)/sqrt2 (the Bell vector, a on
-- the high bit).

prog bell_pair (x : [2]) : [2] {
    new a : [2] @ |0>;
    new b : [2] @ |0>;
    H a;
    CX a b;
    drop (a, b);
    return x
}
