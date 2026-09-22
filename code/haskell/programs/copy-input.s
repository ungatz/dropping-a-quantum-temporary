-- copy-input.s: the program of the statics subsection -- it copies its input into a
-- temporary and forgets the input.  Token-identical to the inline listing
-- there.  It types, and the criterion calls its drop unsafe.
--
-- Site: drop x (depth 0).  Expected: UNSAFE.

prog f (x : [2]) : [2] { new t : [2] @ |0>; CX x t; drop x; return t }
