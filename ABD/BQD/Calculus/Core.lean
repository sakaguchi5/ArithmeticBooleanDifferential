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

/-- `K`: both-active quadrant. -/
def K (D : Decomp α) : Finset α :=
  D.L ∩ D.R

/-- `P`: left-only quadrant. -/
def P (D : Decomp α) : Finset α :=
  D.L \ D.R

/-- `Q`: right-only quadrant. -/
def Q (D : Decomp α) : Finset α :=
  D.R \ D.L

/-- `Z`: neither-active quadrant inside the common universe. -/
def Z (D : Decomp α) : Finset α :=
  D.U \ (D.L ∪ D.R)

/-- The active union of the two objects. -/
def active (D : Decomp α) : Finset α :=
  D.L ∪ D.R

/-- The exclusive-active part, i.e. Boolean xor of the active sets. -/
def exclusive (D : Decomp α) : Finset α :=
  D.P ∪ D.Q

@[simp] theorem K_def (D : Decomp α) : D.K = D.L ∩ D.R := rfl
@[simp] theorem P_def (D : Decomp α) : D.P = D.L \ D.R := rfl
@[simp] theorem Q_def (D : Decomp α) : D.Q = D.R \ D.L := rfl
@[simp] theorem Z_def (D : Decomp α) : D.Z = D.U \ (D.L ∪ D.R) := rfl
@[simp] theorem active_def (D : Decomp α) : D.active = D.L ∪ D.R := rfl
@[simp] theorem exclusive_def (D : Decomp α) : D.exclusive = D.P ∪ D.Q := rfl

/-- `K` lies inside the common universe. -/
theorem K_subset_U (D : Decomp α) : D.K ⊆ D.U := by
  intro x hx
  exact D.hL ((Finset.mem_inter.mp hx).1)

/-- `P` lies inside the common universe. -/
theorem P_subset_U (D : Decomp α) : D.P ⊆ D.U := by
  intro x hx
  exact D.hL ((Finset.mem_sdiff.mp hx).1)

/-- `Q` lies inside the common universe. -/
theorem Q_subset_U (D : Decomp α) : D.Q ⊆ D.U := by
  intro x hx
  exact D.hR ((Finset.mem_sdiff.mp hx).1)

/-- `Z` lies inside the common universe. -/
theorem Z_subset_U (D : Decomp α) : D.Z ⊆ D.U := by
  intro x hx
  exact (Finset.mem_sdiff.mp hx).1

end Decomp
end BQD
end ABD
