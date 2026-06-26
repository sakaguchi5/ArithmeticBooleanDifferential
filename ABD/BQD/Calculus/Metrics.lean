import Mathlib.Data.Finset.Card
import ABD.BQD.Calculus.Idempotent

namespace ABD
namespace BQD
namespace Decomp

variable {α : Type u} [DecidableEq α]

/-- Size of the both-active quadrant. -/
def kCount (D : Decomp α) : ℕ := D.K.card

/-- Size of the left-only quadrant. -/
def pCount (D : Decomp α) : ℕ := D.P.card

/-- Size of the right-only quadrant. -/
def qCount (D : Decomp α) : ℕ := D.Q.card

/-- Size of the neither-active quadrant. -/
def zCount (D : Decomp α) : ℕ := D.Z.card

/-- Hamming/xor distance between the two active sets. -/
def xorCount (D : Decomp α) : ℕ :=
  D.P.card + D.Q.card

/-- Alias for `xorCount`, emphasizing metric interpretation. -/
def hammingDistance (D : Decomp α) : ℕ :=
  D.xorCount

/-- Common-active count. -/
def commonCount (D : Decomp α) : ℕ :=
  D.K.card

/-- Union-active count. -/
def unionCount (D : Decomp α) : ℕ :=
  D.active.card

/-- Absolute imbalance between left-only and right-only quadrants. -/
def imbalance (D : Decomp α) : ℕ :=
  if D.P.card ≤ D.Q.card then D.Q.card - D.P.card else D.P.card - D.Q.card

@[simp] theorem hammingDistance_eq_xorCount (D : Decomp α) :
    D.hammingDistance = D.xorCount := rfl

@[simp] theorem xorCount_eq_pCount_add_qCount (D : Decomp α) :
    D.xorCount = D.pCount + D.qCount := rfl

@[simp] theorem commonCount_eq_kCount (D : Decomp α) :
    D.commonCount = D.kCount := rfl

end Decomp
end BQD
end ABD
