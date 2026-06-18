import ABD.ABD.Core.PrimeSupport

namespace ABD

/-- The valuation layer: the exponent of `p` in `n`, via `Nat.factorization`. -/
def val (n p : ℕ) : ℕ :=
  n.factorization p

@[simp]
theorem val_eq_factorization (n p : ℕ) :
    val n p = n.factorization p := by
  rfl

@[simp]
theorem supp_eq_factorization_support (n : ℕ) :
    supp n = n.factorization.support := by
  rfl

end ABD
