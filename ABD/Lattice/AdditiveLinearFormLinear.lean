import ABD.Lattice.Kernel

namespace ABD

open BigOperators

/-- The formal derivative is additive in the tangent vector. -/
private theorem formalDeriv_add_tangent
    (S : Finset ℕ) (x y : Tangent S) (n : ℕ) :
    formalDeriv S (x + y) n = formalDeriv S x n + formalDeriv S y n := by
  unfold formalDeriv
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The formal derivative commutes with negating the tangent vector. -/
private theorem formalDeriv_neg_tangent
    (S : Finset ℕ) (x : Tangent S) (n : ℕ) :
    formalDeriv S (-x) n = -formalDeriv S x n := by
  unfold formalDeriv
  simp [Pi.neg_apply]

/-- The formal derivative is homogeneous in the tangent vector. -/
private theorem formalDeriv_zsmul_tangent
    (S : Finset ℕ) (k : ℤ) (x : Tangent S) (n : ℕ) :
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

/-- `AdditiveLinearForm` is additive in the tangent vector. -/
theorem additiveLinearForm_add
    (S : Finset ℕ) (x y : Tangent S) (a b c : ℕ) :
    AdditiveLinearForm S (x + y) a b c =
      AdditiveLinearForm S x a b c + AdditiveLinearForm S y a b c := by
  unfold AdditiveLinearForm
  rw [formalDeriv_add_tangent S x y a]
  rw [formalDeriv_add_tangent S x y b]
  rw [formalDeriv_add_tangent S x y c]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- `AdditiveLinearForm` commutes with negating the tangent vector. -/
theorem additiveLinearForm_neg
    (S : Finset ℕ) (x : Tangent S) (a b c : ℕ) :
    AdditiveLinearForm S (-x) a b c =
      -AdditiveLinearForm S x a b c := by
  unfold AdditiveLinearForm
  rw [formalDeriv_neg_tangent S x a]
  rw [formalDeriv_neg_tangent S x b]
  rw [formalDeriv_neg_tangent S x c]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- `AdditiveLinearForm` is homogeneous in the tangent vector. -/
theorem additiveLinearForm_zsmul
    (S : Finset ℕ) (k : ℤ) (x : Tangent S) (a b c : ℕ) :
    AdditiveLinearForm S (k • x) a b c =
      k * AdditiveLinearForm S x a b c := by
  unfold AdditiveLinearForm
  rw [formalDeriv_zsmul_tangent S k x a]
  rw [formalDeriv_zsmul_tangent S k x b]
  rw [formalDeriv_zsmul_tangent S k x c]
  simp [sub_eq_add_neg, mul_add, mul_neg, add_assoc]

/-- `AdditiveLinearForm` sends the zero tangent to zero. -/
@[simp] theorem additiveLinearForm_zeroTangent
    (S : Finset ℕ) (a b c : ℕ) :
    AdditiveLinearForm S (zeroTangent S) a b c = 0 := by
  simp [AdditiveLinearForm]

/-- The coefficient-sum presentation is additive in the tangent vector. -/
theorem additiveLinearFormByCoeff_add
    (S : Finset ℕ) (x y : Tangent S) (a b c : ℕ) :
    AdditiveLinearFormByCoeff S (x + y) a b c =
      AdditiveLinearFormByCoeff S x a b c +
        AdditiveLinearFormByCoeff S y a b c := by
  unfold AdditiveLinearFormByCoeff
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The coefficient-sum presentation commutes with negating the tangent vector. -/
theorem additiveLinearFormByCoeff_neg
    (S : Finset ℕ) (x : Tangent S) (a b c : ℕ) :
    AdditiveLinearFormByCoeff S (-x) a b c =
      -AdditiveLinearFormByCoeff S x a b c := by
  unfold AdditiveLinearFormByCoeff
  simp [Pi.neg_apply]

/-- The coefficient-sum presentation is homogeneous in the tangent vector. -/
theorem additiveLinearFormByCoeff_zsmul
    (S : Finset ℕ) (k : ℤ) (x : Tangent S) (a b c : ℕ) :
    AdditiveLinearFormByCoeff S (k • x) a b c =
      k * AdditiveLinearFormByCoeff S x a b c := by
  unfold AdditiveLinearFormByCoeff
  calc
    (∑ hp : {p : ℕ // p ∈ S}, addCoeff a b c hp.1 * (k • x) hp)
        = ∑ hp : {p : ℕ // p ∈ S}, k * (addCoeff a b c hp.1 * x hp) := by
            apply Finset.sum_congr rfl
            intro hp _
            simp [Pi.smul_apply, mul_left_comm, mul_comm]
    _ = k * ∑ hp : {p : ℕ // p ∈ S}, addCoeff a b c hp.1 * x hp := by
            simpa using
              (Finset.mul_sum
                (s := (Finset.univ : Finset {p : ℕ // p ∈ S}))
                (f := fun hp : {p : ℕ // p ∈ S} => addCoeff a b c hp.1 * x hp)
                k).symm

end ABD
