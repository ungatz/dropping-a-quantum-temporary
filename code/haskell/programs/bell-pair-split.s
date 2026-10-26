-- bell-pair-split.s: which program a context compares.  Token-identical
-- circuit to bell-pair.s -- the same Bell pair, H then CX -- but the two
-- temporaries are dropped one register at a time instead of as one tuple.
-- Both drops are UNSAFE: the Bell vector is not a product state, so
-- dropping a alone leaves a block that cannot be factored from the rest
-- (b and x); and once a is gone, dropping b finds the rest of the state
-- still carrying the hidden register a it was entangled with.  Nothing is
-- emitted at either drop.
--
-- Sites: drop a (depth 0), drop b (depth 0).  Expected: drop a UNSAFE (the
-- block a, the rest b and x: the Bell vector is no product); drop b
-- UNSAFE (the rest contains the hidden a).

prog bell_pair_split (x : [2]) : [2] {
    new a : [2] @ |0>;
    new b : [2] @ |0>;
    H a;
    CX a b;
    drop a;
    drop b;
    return x
}
