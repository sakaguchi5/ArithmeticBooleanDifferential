import Mathlib.Data.Finset.Basic

namespace ABD
namespace BQD

/-- Boolean Quadrant Decomposition data.

`U` is the common universe.
`L` is the active set of the left object.
`R` is the active set of the right object.

No arithmetic, bit, or prime-support meaning is assumed here. -/
structure Decomp (α : Type u) [DecidableEq α] where
  U : Finset α
  L : Finset α
  R : Finset α
  hL : L ⊆ U
  hR : R ⊆ U

namespace Decomp

variable {α : Type u} [DecidableEq α]

/-- `B`: both-active atom, i.e. left and right are both active. -/
def B (D : Decomp α) : Finset α :=
  D.L ∩ D.R

/-- `LO`: left-only atom, i.e. left is active and right is inactive. -/
def LO (D : Decomp α) : Finset α :=
  D.L \ D.R

/-- `RO`: right-only atom, i.e. right is active and left is inactive. -/
def RO (D : Decomp α) : Finset α :=
  D.R \ D.L

/-- `N`: neither-active atom inside the common universe. -/
def N (D : Decomp α) : Finset α :=
  D.U \ (D.L ∪ D.R)

/-- Descriptive alias for `B`. -/
abbrev Both (D : Decomp α) : Finset α := D.B

/-- Descriptive alias for `LO`. -/
abbrev LeftOnly (D : Decomp α) : Finset α := D.LO

/-- Descriptive alias for `RO`. -/
abbrev RightOnly (D : Decomp α) : Finset α := D.RO

/-- Descriptive alias for `N`. -/
abbrev Neither (D : Decomp α) : Finset α := D.N

/-- The active union of the two objects. -/
def active (D : Decomp α) : Finset α :=
  D.L ∪ D.R

/-- The exclusive-active part, i.e. Boolean xor of the active sets. -/
def exclusive (D : Decomp α) : Finset α :=
  D.LO ∪ D.RO

@[simp] theorem B_def (D : Decomp α) : D.B = D.L ∩ D.R := rfl
@[simp] theorem LO_def (D : Decomp α) : D.LO = D.L \ D.R := rfl
@[simp] theorem RO_def (D : Decomp α) : D.RO = D.R \ D.L := rfl
@[simp] theorem N_def (D : Decomp α) : D.N = D.U \ (D.L ∪ D.R) := rfl
@[simp] theorem Both_def (D : Decomp α) : D.Both = D.B := rfl
@[simp] theorem LeftOnly_def (D : Decomp α) : D.LeftOnly = D.LO := rfl
@[simp] theorem RightOnly_def (D : Decomp α) : D.RightOnly = D.RO := rfl
@[simp] theorem Neither_def (D : Decomp α) : D.Neither = D.N := rfl
@[simp] theorem active_def (D : Decomp α) : D.active = D.L ∪ D.R := rfl
@[simp] theorem exclusive_def (D : Decomp α) : D.exclusive = D.LO ∪ D.RO := rfl

/-- `B` lies inside the common universe. -/
theorem B_subset_U (D : Decomp α) : D.B ⊆ D.U := by
  intro x hx
  exact D.hL ((Finset.mem_inter.mp hx).1)

/-- `LO` lies inside the common universe. -/
theorem LO_subset_U (D : Decomp α) : D.LO ⊆ D.U := by
  intro x hx
  exact D.hL ((Finset.mem_sdiff.mp hx).1)

/-- `RO` lies inside the common universe. -/
theorem RO_subset_U (D : Decomp α) : D.RO ⊆ D.U := by
  intro x hx
  exact D.hR ((Finset.mem_sdiff.mp hx).1)

/-- `N` lies inside the common universe. -/
theorem N_subset_U (D : Decomp α) : D.N ⊆ D.U := by
  intro x hx
  exact (Finset.mem_sdiff.mp hx).1

end Decomp
end BQD
end ABD
