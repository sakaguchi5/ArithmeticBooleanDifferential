import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic

namespace ABD3

/-- Minimal ABC triple data used by ABD3.

ABD3 deliberately keeps only the additive triple itself here.  Prime support,
radicals, and radical-small inequalities are derived data, not stored fields. -/
structure ABCData where
  A : ℕ
  B : ℕ
  C : ℕ
  h_add : A + B = C

namespace ABCData

/-- Primitive condition for the additive triple. -/
def Primitive (T : ABCData) : Prop :=
  Nat.Coprime T.A T.B

/-- First-pass non-exceptional boundary used by the E2 route. -/
def NonExceptional (T : ABCData) : Prop :=
  T.A ≠ 1 ∧ T.B ≠ 1

/-- The one-sided unit boundary used as the first concrete exceptional pattern. -/
def UnitBoundary (T : ABCData) : Prop :=
  T.A = 1 ∨ T.B = 1

/-- `NonExceptional` is exactly the negation of the first-pass unit boundary. -/
theorem nonExceptional_iff_not_unitBoundary (T : ABCData) :
    T.NonExceptional ↔ ¬ T.UnitBoundary := by
  unfold NonExceptional UnitBoundary
  constructor
  · intro h hu
    rcases hu with hA | hB
    · exact h.1 hA
    · exact h.2 hB
  · intro h
    constructor
    · intro hA
      exact h (Or.inl hA)
    · intro hB
      exact h (Or.inr hB)

end ABCData
end ABD3
