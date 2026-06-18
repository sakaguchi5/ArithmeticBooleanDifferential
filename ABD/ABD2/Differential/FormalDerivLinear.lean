import ABD.ABD2.Differential.DerivCoeff

namespace ABD2

open BigOperators

/-- Formal arithmetic derivative reconstructed from prime-direction values. -/
def formalDeriv (S : Finset ℕ) (x : Tangent S) (n : ℕ) : ℤ :=
  ∑ hp : {p : ℕ // p ∈ S}, derivCoeff n hp.1 * x hp

@[simp]
theorem formalDeriv_zero (S : Finset ℕ) (n : ℕ) :
    formalDeriv S (0 : Tangent S) n = 0 := by
  simp [formalDeriv]

@[simp]
theorem formalDeriv_add (S : Finset ℕ) (x y : Tangent S) (n : ℕ) :
    formalDeriv S (x + y) n = formalDeriv S x n + formalDeriv S y n := by
  unfold formalDeriv
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[simp]
theorem formalDeriv_neg (S : Finset ℕ) (x : Tangent S) (n : ℕ) :
    formalDeriv S (-x) n = -formalDeriv S x n := by
  unfold formalDeriv
  simp [Pi.neg_apply]

@[simp]
theorem formalDeriv_sub (S : Finset ℕ) (x y : Tangent S) (n : ℕ) :
    formalDeriv S (x - y) n = formalDeriv S x n - formalDeriv S y n := by
  simp [sub_eq_add_neg, formalDeriv_add, formalDeriv_neg]

@[simp]
theorem formalDeriv_smul (S : Finset ℕ) (k : ℤ) (x : Tangent S) (n : ℕ) :
    formalDeriv S (k • x) n = k * formalDeriv S x n := by
  unfold formalDeriv
  calc
    (∑ hp : {p : ℕ // p ∈ S}, derivCoeff n hp.1 * (k • x) hp)
        = ∑ hp : {p : ℕ // p ∈ S}, k * (derivCoeff n hp.1 * x hp) := by
          apply Finset.sum_congr rfl
          intro hp _
          simp [Pi.smul_apply, mul_left_comm, mul_comm]
    _ = k * ∑ hp : {p : ℕ // p ∈ S}, derivCoeff n hp.1 * x hp := by
          simpa using
            (Finset.mul_sum
              (s := (Finset.univ : Finset {p : ℕ // p ∈ S}))
              (f := fun hp : {p : ℕ // p ∈ S} => derivCoeff n hp.1 * x hp)
              k).symm

/-- Formal derivative as a linear map in the tangent vector. -/
noncomputable def formalDerivLinear (S : Finset ℕ) (n : ℕ) :
    Tangent S →ₗ[ℤ] ℤ where
  toFun x := formalDeriv S x n
  map_add' := by
    intro x y
    exact formalDeriv_add S x y n
  map_smul' := by
    intro k x
    exact formalDeriv_smul S k x n

@[simp]
theorem formalDerivLinear_apply (S : Finset ℕ) (n : ℕ) (x : Tangent S) :
    formalDerivLinear S n x = formalDeriv S x n := by
  rfl

end ABD2
