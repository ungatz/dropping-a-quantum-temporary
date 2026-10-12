-- copy-input.s: copies its input into a temporary and forgets the input.
-- The program is well typed, but its drop is unsafe.
--
-- Site: drop x (depth 0).  Expected: UNSAFE.

prog f (x : [2]) : [2] { new t : [2] @ |0>; CX x t; drop x; return t }
