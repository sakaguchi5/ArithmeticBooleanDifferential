import ABD.ABD2.Core.Mask

namespace ABD2

/-- Boolean masks are idempotent projections. -/
theorem supportMask_idempotent
    (S M : Finset ℕ) (x : Tangent S) :
    supportMask S M (supportMask S M x) = supportMask S M x := by
  funext p
  by_cases hp : p.1 ∈ M <;> simp [supportMask, hp]

/-- Composition of masks is Boolean AND/intersection. -/
theorem supportMask_comp
    (S M N : Finset ℕ) (x : Tangent S) :
    supportMask S M (supportMask S N x) = supportMask S (M ∩ N) x := by
  funext p
  by_cases hM : p.1 ∈ M <;> by_cases hN : p.1 ∈ N <;>
    simp [supportMask, hM, hN]

/-- Mask composition is commutative, because intersection is commutative. -/
theorem supportMask_comm
    (S M N : Finset ℕ) (x : Tangent S) :
    supportMask S M (supportMask S N x) =
      supportMask S N (supportMask S M x) := by
  rw [supportMask_comp, supportMask_comp]
  funext p
  by_cases hM : p.1 ∈ M <;> by_cases hN : p.1 ∈ N <;>
    simp [supportMask, hM, hN,  and_comm]

/-- If two masks are disjoint, applying one after the other gives zero. -/
theorem supportMask_comp_eq_zero_of_disjoint
    (S M N : Finset ℕ) (hdisj : Disjoint M N) (x : Tangent S) :
    supportMask S M (supportMask S N x) = 0 := by
  funext p
  by_cases hM : p.1 ∈ M <;> by_cases hN : p.1 ∈ N
  · have hfalse : False := by
      exact Finset.disjoint_left.mp hdisj hM hN
    exact False.elim hfalse
  · simp [supportMask, hM, hN]
  · simp [supportMask, hM]
  · simp [supportMask, hM]

/-- Disjoint union of masks is addition of orthogonal projections. -/
theorem supportMask_union_eq_add_of_disjoint
    (S M N : Finset ℕ) (hdisj : Disjoint M N) (x : Tangent S) :
    supportMask S (M ∪ N) x = supportMask S M x + supportMask S N x := by
  funext p
  by_cases hM : p.1 ∈ M <;> by_cases hN : p.1 ∈ N
  · have hfalse : False := by
      exact Finset.disjoint_left.mp hdisj hM hN
    exact False.elim hfalse
  · simp [supportMask, hM, hN]
  · simp [supportMask, hM, hN]
  · simp [supportMask, hM, hN]

/-- If a support is covered by two disjoint masks, every tangent splits into two
orthogonal Boolean pieces. -/
theorem tangent_eq_mask_add_mask_of_union_eq_support
    (S M N : Finset ℕ) (hcover : M ∪ N = S) (hdisj : Disjoint M N)
    (x : Tangent S) :
    x = supportMask S M x + supportMask S N x := by
  rw [← supportMask_union_eq_add_of_disjoint S M N hdisj x]
  simp [hcover]

end ABD2
