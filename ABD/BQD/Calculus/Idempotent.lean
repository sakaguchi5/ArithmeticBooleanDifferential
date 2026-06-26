import ABD.BQD.Calculus.Core

namespace ABD
namespace BQD
namespace Decomp

variable {α : Type u} [DecidableEq α]

/-- The both-active and left-only atoms are orthogonal. -/
@[simp] theorem B_inter_LO_eq_empty (D : Decomp α) :
    D.B ∩ D.LO = (∅ : Finset α) := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [B, LO, hxL]

/-- The both-active and right-only atoms are orthogonal. -/
@[simp] theorem B_inter_RO_eq_empty (D : Decomp α) :
    D.B ∩ D.RO = (∅ : Finset α) := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [B, RO, hxL, hxR]

/-- The both-active and neither-active atoms are orthogonal. -/
@[simp] theorem B_inter_N_eq_empty (D : Decomp α) :
    D.B ∩ D.N = (∅ : Finset α) := by
  ext x
  by_cases hxU : x ∈ D.U <;> by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [B, N, hxU, hxL, hxR]

/-- The left-only and right-only atoms are orthogonal. -/
@[simp] theorem LO_inter_RO_eq_empty (D : Decomp α) :
    D.LO ∩ D.RO = (∅ : Finset α) := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [LO, RO, hxL, hxR]

/-- The left-only and neither-active atoms are orthogonal. -/
@[simp] theorem LO_inter_N_eq_empty (D : Decomp α) :
    D.LO ∩ D.N = (∅ : Finset α) := by
  ext x
  by_cases hxU : x ∈ D.U <;> by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [LO, N, hxU, hxL, hxR]

/-- The right-only and neither-active atoms are orthogonal. -/
@[simp] theorem RO_inter_N_eq_empty (D : Decomp α) :
    D.RO ∩ D.N = (∅ : Finset α) := by
  ext x
  by_cases hxU : x ∈ D.U <;> by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [RO, N, hxU, hxL, hxR]

/-- Reconstruct the left active set from `B` and `LO`. -/
@[simp] theorem B_union_LO_eq_L (D : Decomp α) :
    D.B ∪ D.LO = D.L := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [B, LO, hxL, hxR]

/-- Reconstruct the right active set from `B` and `RO`. -/
@[simp] theorem B_union_RO_eq_R (D : Decomp α) :
    D.B ∪ D.RO = D.R := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [B, RO, hxL, hxR]

/-- The nonzero-active part is `B ∪ LO ∪ RO`, i.e. `L ∪ R`. -/
@[simp] theorem B_union_LO_union_RO_eq_active (D : Decomp α) :
    D.B ∪ D.LO ∪ D.RO = D.active := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [B, LO, RO, active, hxL, hxR]

/-- The exclusive-active part is the union of the left-only and right-only atoms. -/
@[simp] theorem exclusive_eq_LO_union_RO (D : Decomp α) :
    D.exclusive = D.LO ∪ D.RO := rfl

/-- The four atoms cover the common universe. -/
@[simp] theorem B_union_LO_union_RO_union_N_eq_U (D : Decomp α) :
    D.B ∪ D.LO ∪ D.RO ∪ D.N = D.U := by
  ext x
  by_cases hxU : x ∈ D.U
  · by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
      simp [B, LO, RO, N, hxU, hxL, hxR]
  · have hxL : x ∉ D.L := by
      intro h
      exact hxU (D.hL h)
    have hxR : x ∉ D.R := by
      intro h
      exact hxU (D.hR h)
    simp [B, LO, RO, N, hxU, hxL, hxR]

end Decomp
end BQD
end ABD
