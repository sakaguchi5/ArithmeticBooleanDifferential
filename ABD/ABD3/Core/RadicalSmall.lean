import ABD.ABD3.Core.Radical
import ABD.ABD3.Core.Power

namespace ABD3

namespace ABCData

/-- Nat-valued radical-small inequality generated from `A,B,C,N,M`. -/
def RadicalSmallNat (T : ABCData) (P : PowerData) : Prop :=
  T.radABC ^ P.N < T.C ^ P.M

/-- Int-valued radical-small inequality, matching the ABD2 E2 convention. -/
def RadicalSmallInt (T : ABCData) (P : PowerData) : Prop :=
  ((T.radABC : ℤ) ^ P.N) < ((T.C : ℤ) ^ P.M)

/-- Default ABD3 radical-small predicate: the ABD2-compatible integer-power form. -/
def RadicalSmall (T : ABCData) (P : PowerData) : Prop :=
  T.RadicalSmallInt P

/-- Radical-large side, the harmless side used in the E2 contrapositive route. -/
def RadicalLarge (T : ABCData) (P : PowerData) : Prop :=
  ((T.C : ℤ) ^ P.M) ≤ ((T.radABC : ℤ) ^ P.N)

/-- Concrete dangerous normal form generated from `A,B,C,N,M`. -/
def ConcreteDangerNormalForm (T : ABCData) (P : PowerData) : Prop :=
  T.RadicalSmall P ∧ T.NonExceptional

@[simp] theorem radicalSmall_iff_int (T : ABCData) (P : PowerData) :
    T.RadicalSmall P ↔ T.RadicalSmallInt P := by
  rfl

@[simp] theorem concreteDangerNormalForm_iff
    (T : ABCData) (P : PowerData) :
    T.ConcreteDangerNormalForm P ↔ T.RadicalSmall P ∧ T.NonExceptional := by
  rfl

end ABCData
end ABD3
