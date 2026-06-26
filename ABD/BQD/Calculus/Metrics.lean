import Mathlib.Data.Finset.Card
import ABD.BQD.Calculus.Idempotent

namespace ABD
namespace BQD
namespace Decomp

variable {α : Type u} [DecidableEq α]

/-- Size of the both-active atom. -/
def bCount (D : Decomp α) : ℕ := D.B.card

/-- Size of the left-only atom. -/
def loCount (D : Decomp α) : ℕ := D.LO.card

/-- Size of the right-only atom. -/
def roCount (D : Decomp α) : ℕ := D.RO.card

/-- Size of the neither-active atom. -/
def nCount (D : Decomp α) : ℕ := D.N.card

/-- Hamming/xor distance between the two active sets. -/
def xorCount (D : Decomp α) : ℕ :=
  D.LO.card + D.RO.card

/-- Alias for `xorCount`, emphasizing metric interpretation. -/
def hammingDistance (D : Decomp α) : ℕ :=
  D.xorCount

/-- Common-active count. -/
def commonCount (D : Decomp α) : ℕ :=
  D.B.card

/-- Union-active count. -/
def unionCount (D : Decomp α) : ℕ :=
  D.active.card

/-- Absolute imbalance between left-only and right-only atoms. -/
def imbalance (D : Decomp α) : ℕ :=
  if D.LO.card ≤ D.RO.card then D.RO.card - D.LO.card else D.LO.card - D.RO.card

@[simp] theorem hammingDistance_eq_xorCount (D : Decomp α) :
    D.hammingDistance = D.xorCount := rfl

@[simp] theorem xorCount_eq_loCount_add_roCount (D : Decomp α) :
    D.xorCount = D.loCount + D.roCount := rfl

@[simp] theorem commonCount_eq_bCount (D : Decomp α) :
    D.commonCount = D.bCount := rfl

end Decomp
end BQD
end ABD
