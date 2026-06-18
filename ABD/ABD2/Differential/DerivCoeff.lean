import ABD.ABD2.Module.All

namespace ABD2

/-- p-adic exponent layer, via `Nat.factorization`. -/
def val (n p : ℕ) : ℕ :=
  n.factorization p

/-- Coefficient of the prime-direction value `D(p)` in the formal derivative of `n`. -/
def derivCoeff (n p : ℕ) : ℤ :=
  (val n p : ℤ) * ((n / p : ℕ) : ℤ)

/-- Outside the prime support of `n`, the derivative coefficient vanishes. -/
theorem derivCoeff_eq_zero_of_not_mem_PrimeSupport
    (n p : ℕ) (hp : p ∉ PrimeSupport n) :
    derivCoeff n p = 0 := by
  unfold derivCoeff val PrimeSupport at *
  have hp0 : n.factorization p = 0 := by
    exact Finsupp.notMem_support_iff.mp hp
  simp [hp0]

end ABD2
