import ABD.ABD2.Differential.FormalDerivLinear

namespace ABD2

open BigOperators

/-- If all coefficients outside a mask vanish, then the formal derivative only
sees the masked part of the tangent vector. -/
theorem formalDeriv_eq_mask_of_coeff_zero_off
    (S M : Finset ℕ) (x : Tangent S) (n : ℕ)
    (hcoeff : ∀ p : {p : ℕ // p ∈ S}, p.1 ∉ M → derivCoeff n p.1 = 0) :
    formalDeriv S (supportMask S M x) n = formalDeriv S x n := by
  unfold formalDeriv
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hm : p.1 ∈ M
  · simp [supportMask, hm]
  · have hc := hcoeff p hm
    simp [supportMask, hm, hc]

/-- The formal derivative of `n` only sees the prime support of `n`. -/
theorem formalDeriv_eq_PrimeSupport_mask
    (S : Finset ℕ) (x : Tangent S) (n : ℕ) :
    formalDeriv S (supportMask S (PrimeSupport n) x) n = formalDeriv S x n := by
  exact formalDeriv_eq_mask_of_coeff_zero_off S (PrimeSupport n) x n
    (by
      intro p hp
      exact derivCoeff_eq_zero_of_not_mem_PrimeSupport n p.1 hp)

/-- Equivalently, the formal derivative ignores the complement of `PrimeSupport n`. -/
theorem formalDerivLinear_comp_mask_PrimeSupport
    (S : Finset ℕ) (n : ℕ) :
    (formalDerivLinear S n).comp (Projection S (PrimeSupport n)) =
      formalDerivLinear S n := by
  ext x
  exact formalDeriv_eq_PrimeSupport_mask S x n

end ABD2
