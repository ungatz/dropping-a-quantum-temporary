-- temp-general.s: the general measurement-based uncomputation of Kornerup,
-- Sadun and Soloveichik, "The Spooky Pebble Game", arXiv:2110.08973v1,
-- Figure 1, instantiated at f(x,y) = x AND y.
--
-- Figure 1 in five boxes: H on the temporary; measure it, binding b; flip it
-- back to |0> when b = 1; recompute f with U_f; a Z on that recomputed value
-- when b = 1, which cancels the (-1)^(b f) phase the measurement left on the
-- input register; and a last U_f to zero the temporary.
--
-- Unlike temp-and.s, no step here uses that f is an AND.  temp-and.s corrects
-- with one diag on x,y because (-1)^(x AND y) happens to BE a gate; Figure 1
-- cannot assume that, so it buys the same correction with two more U_f calls.
-- Same verdict, three Toffolis instead of one.
--
-- Site: drop a (depth 1).  Expected: SAFE on both records, on the basis
-- vector of level 0.

prog temp_general (x : [2], y : [2]) : [2] * [2] {
    new a : [2] @ |0>;
    CCX x y a;               -- U_f: a := x AND y.  Figure 1 starts here.
    H a;
    b = lift[{1}] a;
    if b { X a; } else { }   -- reset the temporary to |0>, either outcome
    CCX x y a;               -- U_f again: recompute f into the fresh |0>
    if b { Z a; } else { }   -- the correction, on the recomputed value
    CCX x y a;               -- U_f a third time: zero the temporary
    drop a;
    return (x, y)
}
