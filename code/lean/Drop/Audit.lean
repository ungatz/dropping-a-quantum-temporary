import Drop

/-!
# Axiom audit

`#print axioms` on each headline statement. Every one reports only
`propext`, `Classical.choice` and `Quot.sound`.
-/

-- the criterion: a typed program is weakenable iff its drop is safe
#print axioms Calculus.typed_weakening_iff_discardSafe
#print axioms Calculus.sourceWeakenable_iff_discardSafe_and_isometric
-- drop safety is a constant final state of the temporary
#print axioms SourceLanguage.discardSafe_iff_temporary_fixed
-- and it is erasability of the temporary in the dilation picture
#print axioms Dilation.discardSafe_iff_erasable
#print axioms Dilation.typed_weakening_iff_erasable
-- the core
#print axioms Drop.gram_sq
#print axioms Drop.traceVisible_joint
#print axioms Drop.local_comp
#print axioms Drop.exists_recordExact_iff
#print axioms Drop.exists_recordExact_singleton_iff
#print axioms Drop.sqrt_add_le_two_sqrt
