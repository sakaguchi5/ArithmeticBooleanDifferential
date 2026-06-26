import ABD.BQD.Calculus.Core

namespace ABD
namespace BQD
namespace Decomp

variable {α : Type u} [DecidableEq α]

/-- The both-active and left-only quadrants are orthogonal. -/
@[simp] theorem K_inter_P_eq_empty (D : Decomp α) :
    D.K ∩ D.P = (∅ : Finset α) := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [K, P, hxL]

/-- The both-active and right-only quadrants are orthogonal. -/
@[simp] theorem K_inter_Q_eq_empty (D : Decomp α) :
    D.K ∩ D.Q = (∅ : Finset α) := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [K, Q, hxL, hxR]

/-- The both-active and neither-active quadrants are orthogonal. -/
@[simp] theorem K_inter_Z_eq_empty (D : Decomp α) :
    D.K ∩ D.Z = (∅ : Finset α) := by
  ext x
  by_cases hxU : x ∈ D.U <;> by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [K, Z, hxU, hxL, hxR]

/-- The left-only and right-only quadrants are orthogonal. -/
@[simp] theorem P_inter_Q_eq_empty (D : Decomp α) :
    D.P ∩ D.Q = (∅ : Finset α) := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [P, Q, hxL, hxR]

/-- The left-only and neither-active quadrants are orthogonal. -/
@[simp] theorem P_inter_Z_eq_empty (D : Decomp α) :
    D.P ∩ D.Z = (∅ : Finset α) := by
  ext x
  by_cases hxU : x ∈ D.U <;> by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [P, Z, hxU, hxL, hxR]

/-- The right-only and neither-active quadrants are orthogonal. -/
@[simp] theorem Q_inter_Z_eq_empty (D : Decomp α) :
    D.Q ∩ D.Z = (∅ : Finset α) := by
  ext x
  by_cases hxU : x ∈ D.U <;> by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [Q, Z, hxU, hxL, hxR]

/-- Reconstruct the left active set from `K` and `P`. -/
@[simp] theorem K_union_P_eq_L (D : Decomp α) :
    D.K ∪ D.P = D.L := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [K, P, hxL, hxR]

/-- Reconstruct the right active set from `K` and `Q`. -/
@[simp] theorem K_union_Q_eq_R (D : Decomp α) :
    D.K ∪ D.Q = D.R := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [K, Q, hxL, hxR]

/-- The nonzero-active part is `K ∪ P ∪ Q`, i.e. `L ∪ R`. -/
@[simp] theorem K_union_P_union_Q_eq_active (D : Decomp α) :
    D.K ∪ D.P ∪ D.Q = D.active := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [K, P, Q, active, hxL, hxR]

/-- The exclusive-active part is the union of the left-only and right-only quadrants. -/
@[simp] theorem exclusive_eq_P_union_Q (D : Decomp α) :
    D.exclusive = D.P ∪ D.Q := rfl

/-- The four quadrants cover the common universe. -/
@[simp] theorem K_union_P_union_Q_union_Z_eq_U (D : Decomp α) :
    D.K ∪ D.P ∪ D.Q ∪ D.Z = D.U := by
  ext x
  by_cases hxU : x ∈ D.U
  · by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
      simp [K, P, Q, Z, hxU, hxL, hxR]
  · have hxL : x ∉ D.L := by
      intro h
      exact hxU (D.hL h)
    have hxR : x ∉ D.R := by
      intro h
      exact hxU (D.hR h)
    simp [K, P, Q, Z, hxU, hxL, hxR]

end Decomp
end BQD
end ABD
