-- a-then-u.s: program (a) of the introduction with its return replaced by a
-- second allocation, the smaller reuse example of the paper's compiler
-- subsection ("Replacing program (a)'s return by new u : [2] @ |1>; return (v,u)").
-- The drop of t is safe with certificate |+>; compile-reuse restores t to |0>
-- with one H-equivalent gate and prepares u on the same qubit, so fresh
-- compilation uses three circuit qubits and reuse two.
--
-- Site: drop t (depth 0).  Expected: SAFE, certificate |+>.

prog a_then_u (v : [2]) : [2] * [2] {
  new t : [2] @ |0>; H t; drop t;
  new u : [2] @ |1>; return (v,u)
}
