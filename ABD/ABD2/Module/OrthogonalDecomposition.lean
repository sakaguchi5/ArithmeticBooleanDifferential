import ABD.ABD2.Module.Projection

namespace ABD2

/-- Three Boolean masks forming an orthogonal decomposition of a support. -/
structure ThreeMaskDecomposition (S A B C : Finset ℕ) : Prop where
  cover : A ∪ B ∪ C = S
  disjAB : Disjoint A B
  disjAC : Disjoint A C
  disjBC : Disjoint B C

/-- Reassemble a tangent vector from three masked pieces. -/
theorem tangent_eq_three_masks
    (S A B C : Finset ℕ) (h : ThreeMaskDecomposition S A B C)
    (x : Tangent S) :
    x = supportMask S A x + supportMask S B x + supportMask S C x := by
  funext p
  have hpS : p.1 ∈ S := p.2
  have hcoverMem : p.1 ∈ A ∪ B ∪ C := by
    simp [h.cover]
  by_cases hA : p.1 ∈ A
  · have hB : p.1 ∉ B := by
      intro hb
      exact Finset.disjoint_left.mp h.disjAB hA hb
    have hC : p.1 ∉ C := by
      intro hc
      exact Finset.disjoint_left.mp h.disjAC hA hc
    simp [supportMask, hA, hB, hC]
  · by_cases hB : p.1 ∈ B
    · have hC : p.1 ∉ C := by
        intro hc
        exact Finset.disjoint_left.mp h.disjBC hB hc
      simp [supportMask, hA, hB, hC]
    · have hC : p.1 ∈ C := by
        simpa [hA, hB] using hcoverMem
      simp [supportMask, hA, hB, hC]

/-- Orthogonality of the first two projections. -/
theorem threeMask_projectionAB_zero
    (S A B C : Finset ℕ) (h : ThreeMaskDecomposition S A B C) (x : Tangent S) :
    supportMask S A (supportMask S B x) = 0 := by
  exact supportMask_comp_eq_zero_of_disjoint S A B h.disjAB x

/-- Orthogonality of the first and third projections. -/
theorem threeMask_projectionAC_zero
    (S A B C : Finset ℕ) (h : ThreeMaskDecomposition S A B C) (x : Tangent S) :
    supportMask S A (supportMask S C x) = 0 := by
  exact supportMask_comp_eq_zero_of_disjoint S A C h.disjAC x

/-- Orthogonality of the second and third projections. -/
theorem threeMask_projectionBC_zero
    (S A B C : Finset ℕ) (h : ThreeMaskDecomposition S A B C) (x : Tangent S) :
    supportMask S B (supportMask S C x) = 0 := by
  exact supportMask_comp_eq_zero_of_disjoint S B C h.disjBC x

end ABD2
