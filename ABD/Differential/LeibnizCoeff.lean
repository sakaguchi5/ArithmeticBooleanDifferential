import ABD.Differential.Leibniz

namespace ABD

/-- Coefficient-level Leibniz identity at one prime direction.

Since `formalDeriv` is a finite sum of `derivCoeff n p * x_p`, this is the
local identity that must eventually be proved from the arithmetic of
`Nat.factorization`.  Keeping it as a named predicate separates the hard
coefficient proof from the purely formal sum-level bridge. -/
def DerivCoeffLeibnizAt (m n p : ℕ) : Prop :=
  derivCoeff (m * n) p =
    (m : ℤ) * derivCoeff n p + (n : ℤ) * derivCoeff m p

@[simp] theorem derivCoeffLeibnizAt_iff (m n p : ℕ) :
    DerivCoeffLeibnizAt m n p ↔
      derivCoeff (m * n) p =
        (m : ℤ) * derivCoeff n p + (n : ℤ) * derivCoeff m p := by
  rfl

/-- Coefficient-level Leibniz identity on every coordinate of a finite support. -/
def DerivCoeffLeibnizOn (S : Finset ℕ) (m n : ℕ) : Prop :=
  ∀ hp : {p : ℕ // p ∈ S}, DerivCoeffLeibnizAt m n hp.1

/-- The formal bridge from coefficient-level Leibniz identities to the
sum-level `LeibnizOn` statement.

This proposition is now theoremized below by finite-sum linearity.  The
remaining arithmetic work is exactly `DerivCoeffLeibnizOn`, i.e. the local
coefficient identity coming from `Nat.factorization`. -/
def CoeffLeibnizBridge (S : Finset ℕ) : Prop :=
  ∀ (x : Tangent S) (m n : ℕ),
    DerivCoeffLeibnizOn S m n → LeibnizOn S x m n

/-- A support has the coefficient-level Leibniz theorem when the local
coefficient identity holds on all of its coordinates. -/
def CoeffLeibnizTheorem (S : Finset ℕ) : Prop :=
  ∀ m n : ℕ, DerivCoeffLeibnizOn S m n

/-- A completed coefficient theorem plus the formal bridge gives the full
unrestricted Leibniz theorem on a fixed support. -/
def LeibnizTheoremFromCoeff (S : Finset ℕ) : Prop :=
  CoeffLeibnizTheorem S ∧ CoeffLeibnizBridge S

/-- Coefficient-level Leibniz identities lift to the finite-sum Leibniz rule.

This is the purely formal part of the Leibniz proof: no arithmetic facts about
`Nat.factorization` are used here.  Once every coordinate satisfies
`DerivCoeffLeibnizAt`, multiplying by the tangent coordinate and summing over
`S` gives `LeibnizOn`. -/
theorem coeffLeibnizBridge (S : Finset ℕ) : CoeffLeibnizBridge S := by
  classical
  intro x m n hcoeff
  unfold LeibnizOn formalDeriv
  calc
    (∑ hp : {p : ℕ // p ∈ S}, derivCoeff (m * n) hp.1 * x hp)
        = ∑ hp : {p : ℕ // p ∈ S},
            ((m : ℤ) * derivCoeff n hp.1 + (n : ℤ) * derivCoeff m hp.1) * x hp := by
          refine Finset.sum_congr rfl ?_
          intro hp _
          rw [hcoeff hp]
    _ = ∑ hp : {p : ℕ // p ∈ S},
            ((m : ℤ) * (derivCoeff n hp.1 * x hp) +
              (n : ℤ) * (derivCoeff m hp.1 * x hp)) := by
          refine Finset.sum_congr rfl ?_
          intro hp _
          simp [add_mul, mul_assoc]
    _ = (m : ℤ) * (∑ hp : {p : ℕ // p ∈ S}, derivCoeff n hp.1 * x hp) +
          (n : ℤ) * (∑ hp : {p : ℕ // p ∈ S}, derivCoeff m hp.1 * x hp) := by
          rw [Finset.sum_add_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- A completed coefficient theorem gives the full Leibniz theorem on a fixed
support, using the theoremized finite-sum bridge. -/
theorem leibnizTheoremFromCoeff_of_coeff
    {S : Finset ℕ} (Hcoeff : CoeffLeibnizTheorem S) :
    LeibnizTheoremFromCoeff S :=
  ⟨Hcoeff, coeffLeibnizBridge S⟩

end ABD
