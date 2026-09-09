-- temp-general-unpaid.s: temp-general.s with the phase correction deleted.
--
-- The measurement in Kornerup, Sadun and Soloveichik's Figure 1 leaves
-- (-1)^(b f(x,y)) on the VISIBLE register and leaves the temporary on a basis
-- vector.  They call that phase a ghost and require it to be paid off before
-- the computation ends.  This file stops at the first highlighted box: the
-- temporary is reset to |0> and dropped with the ghost still unpaid.
--
-- The question this file asks of the criterion: does dropping a temporary
-- become inadmissible because of a defect the drop left somewhere else?
-- The criterion is a statement about the temporary's line, so the expected
-- answer is no -- the drop is ADMISSIBLE here too, and the ghost is invisible
-- to it.  That is not a bug; it is the scope of the criterion, and it is
-- worth having in the corpus as the program that shows where the scope ends.

vis x:2, y:2;
new a:2;
gate CCX x y a;               -- U_f: a := x AND y
gate H a;
lift b = meas a in {1};
if b { gate X a; } else { }   -- reset the temporary to |0>, either outcome
drop a;                       -- dropped with (-1)^(b f) still on x,y
