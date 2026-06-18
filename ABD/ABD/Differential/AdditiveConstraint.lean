import ABD.ABD.Differential.FormalDerivative

namespace ABD

open BigOperators

/-- The derivative candidate is additive on the selected equation `a + b = c`. -/
def AdditiveOn
    (S : Finset ℕ) (x : Tangent S) (a b c : ℕ) : Prop :=
  formalDeriv S x a + formalDeriv S x b = formalDeriv S x c

/-- Coefficient of `x_p` in the additive linear constraint attached to `a + b = c`. -/
def addCoeff (a b c p : ℕ) : ℤ :=
  derivCoeff a p + derivCoeff b p - derivCoeff c p

/-- The additive constraint as a single integer-valued linear form.

This definition is intentionally the difference form.  It makes the first core theorem
`additiveOn_iff_linearForm_zero` completely stable.  The coefficient-level expression
is kept separately as `AdditiveLinearFormByCoeff`.
-/
def AdditiveLinearForm
    (S : Finset ℕ) (x : Tangent S) (a b c : ℕ) : ℤ :=
  formalDeriv S x a + formalDeriv S x b - formalDeriv S x c

/-- The same linear constraint written directly as a coefficient sum over `S`. -/
def AdditiveLinearFormByCoeff
    (S : Finset ℕ) (x : Tangent S) (a b c : ℕ) : ℤ :=
  ∑ hp : {p : ℕ // p ∈ S}, addCoeff a b c hp.1 * x hp

/-- Additivity of the formal derivative on `a + b = c` is equivalent to the
associated linear form being zero. -/
theorem additiveOn_iff_linearForm_zero
    (S : Finset ℕ) (x : Tangent S) (a b c : ℕ) :
    AdditiveOn S x a b c ↔ AdditiveLinearForm S x a b c = 0 := by
  unfold AdditiveOn AdditiveLinearForm
  constructor
  · intro h
    exact sub_eq_zero.mpr h
  · intro h
    exact sub_eq_zero.mp h

@[simp]
theorem additiveOn_zeroTangent
    (S : Finset ℕ) (a b c : ℕ) :
    AdditiveOn S (zeroTangent S) a b c := by
  simp [AdditiveOn]

end ABD
