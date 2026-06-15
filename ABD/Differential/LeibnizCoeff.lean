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

The next proof step is to theoremize this proposition using finite-sum
linearity.  After that, the remaining arithmetic work is exactly
`DerivCoeffLeibnizOn`. -/
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

end ABD
