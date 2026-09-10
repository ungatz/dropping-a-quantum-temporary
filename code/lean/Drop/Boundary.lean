import Mathlib.Data.Set.Basic

/-!
# The constancy lemma

A record-oblivious verdict reads the command and not the measurement record.
It is record-exact on a class when, for every command of the class and every
record that command reaches, the verdict agrees with the safety of the drop
under that record.  A command is outcome-dependent when it has two reachable
records of opposite verdict.

`exists_recordExact_iff`: a class admits a record-exact record-oblivious
verdict exactly when none of its commands is outcome-dependent.  At a
singleton class this says the obstruction is fixed by the command and not by
the verdict chosen.

Exactness is asked at reachable records only, so -- unlike the sound/complete
formulation this replaces -- no convention about unreachable records is
needed, and the `Setting` carries no side hypothesis.
-/

namespace Drop

/-- Commands `C`, records `T`: which records a command reaches, and whether
the drop is safe under one. -/
structure Setting (C T : Type*) where
  reach : C → T → Prop
  safe : C → T → Prop

variable {C T : Type*} (S : Setting C T)

/-- `D` agrees with the safety verdict at every reachable record of every
command of `cls`. -/
def RecordExactOn (D : C → Prop) (cls : Set C) : Prop :=
  ∀ c ∈ cls, ∀ o, S.reach c o → (D c ↔ S.safe c o)

def OutcomeDependent (c : C) : Prop :=
  ∃ o₁ o₂, S.reach c o₁ ∧ S.safe c o₁ ∧ S.reach c o₂ ∧ ¬ S.safe c o₂

/-- The verdict that accepts a command with one safe reachable record. -/
def someSafe (c : C) : Prop := ∃ o, S.reach c o ∧ S.safe c o

theorem someSafe_recordExactOn {cls : Set C}
    (h : ∀ c ∈ cls, ¬ OutcomeDependent S c) : RecordExactOn S (someSafe S) cls := by
  intro c hc o ho
  constructor
  · rintro ⟨o₁, h₁, hs₁⟩
    by_contra hn
    exact h c hc ⟨o₁, o, h₁, hs₁, ho, hn⟩
  · intro hs
    exact ⟨o, ho, hs⟩

/-- The constancy lemma. -/
theorem exists_recordExact_iff (cls : Set C) :
    (∃ D, RecordExactOn S D cls) ↔ ∀ c ∈ cls, ¬ OutcomeDependent S c := by
  constructor
  · rintro ⟨D, hD⟩ c hc ⟨o₁, o₂, h₁, hs₁, h₂, hu₂⟩
    exact hu₂ ((hD c hc o₂ h₂).mp ((hD c hc o₁ h₁).mpr hs₁))
  · intro h
    exact ⟨someSafe S, someSafe_recordExactOn S h⟩

/-- The singleton case: a command admits a record-exact record-oblivious
verdict exactly when it is not outcome-dependent. -/
theorem exists_recordExact_singleton_iff (c : C) :
    (∃ D, RecordExactOn S D {c}) ↔ ¬ OutcomeDependent S c := by
  rw [exists_recordExact_iff]
  constructor
  · intro h; exact h c rfl
  · intro h c' hc'; have : c' = c := hc'; subst this; exact h

end Drop
