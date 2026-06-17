import ABD.Differential.Tangent

namespace ABD

open BigOperators

/-- Coefficient of the prime-direction value `D(p)` in the formal derivative of `n`.

Mathematically this is intended as `v_p(n) * (n / p)`.
-/
def derivCoeff (n p : ℕ) : ℤ :=
  (val n p : ℤ) * ((n / p : ℕ) : ℤ)

/-- Formal arithmetic derivative reconstructed from values on the finite support `S`.

`formalDeriv S x n = Σ_{p∈S} v_p(n) * (n / p) * x_p`.
-/
def formalDeriv (S : Finset ℕ) (x : Tangent S) (n : ℕ) : ℤ :=
  ∑ hp : {p : ℕ // p ∈ S}, derivCoeff n hp.1 * x hp

@[simp]
theorem formalDeriv_zeroTangent (S : Finset ℕ) (n : ℕ) :
    formalDeriv S (zeroTangent S) n = 0 := by
  simp [formalDeriv, zeroTangent]

end ABD
