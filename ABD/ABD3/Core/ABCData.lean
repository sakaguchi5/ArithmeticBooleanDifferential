import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic

namespace ABD3

/-- A positive natural number, stored together with its positivity proof. -/
structure PositiveNat where
  val : ℕ
  pos : 0 < val

/-- Core ABC triple data for ABD3.

An `ABCData` consists of positive natural numbers `A`, `B`, and `C`
with `A + B = C`, together with the primitive condition
Nat.Coprime A.val B.val.

Derived objects such as prime supports, valuations, radicals, and
radical-small inequalities are intentionally not stored here.
-/
structure ABCData where
  A : PositiveNat
  B : PositiveNat
  C : PositiveNat
  h_add : A.val + B.val = C.val
  h_coprime : Nat.Coprime A.val B.val

namespace ABCData

/-- The primitive condition already stored in `ABCData`. -/
def Primitive (T : ABCData) : Prop :=
  Nat.Coprime T.A.val T.B.val

/-- Every `ABCData` is primitive by construction. -/
theorem primitive (T : ABCData) : T.Primitive :=
  T.h_coprime

/-- A-side positivity, available by construction. -/
theorem A_pos (T : ABCData) : 0 < T.A.val :=
  T.A.pos

/-- B-side positivity, available by construction. -/
theorem B_pos (T : ABCData) : 0 < T.B.val :=
  T.B.pos

/-- C-side positivity, available by construction. -/
theorem C_pos (T : ABCData) : 0 < T.C.val :=
  T.C.pos

/-- The non-exceptional boundary condition used in the ABD3/Pasten direction.

The core `ABCData` allows `A = 1` or `B = 1`; those are valid primitive
positive triples, but are separated here as exceptional boundary cases.
-/
def NonExceptional (T : ABCData) : Prop :=
  T.A.val ≠ 1 ∧ T.B.val ≠ 1

/-- The one-sided unit boundary used as the first concrete exceptional pattern. -/
def UnitBoundary (T : ABCData) : Prop :=
  T.A.val = 1 ∨ T.B.val = 1

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
