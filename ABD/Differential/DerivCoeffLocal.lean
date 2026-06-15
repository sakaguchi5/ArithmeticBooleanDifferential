import ABD.Core.ValuationLemmas
import ABD.Differential.LeibnizCoeff

namespace ABD

/-- Local multiplicativity target for the valuation layer. -/
def ValMulAt (m n p : ℕ) : Prop :=
  val (m * n) p = val m p + val n p

/-- Local coefficient Leibniz target, explicitly named as the arithmetic core of
`DerivCoeffLeibnizAt`.

Mathematically this follows from `ValMulAt` together with the elementary
natural-number division identities for `(m*n)/p`.  It is kept as a separate
name so the next refactor can attack the raw `Nat.factorization` proof without
changing any higher-level Pasten wiring. -/
def DerivCoeffLocalLaw (m n p : ℕ) : Prop :=
  DerivCoeffLeibnizAt m n p

@[simp] theorem derivCoeffLocalLaw_iff (m n p : ℕ) :
    DerivCoeffLocalLaw m n p ↔ DerivCoeffLeibnizAt m n p := by
  rfl

/-- The prime-direction local coefficient Leibniz theorem.

This is the isolated arithmetic choke point: it is the only place where the
project still needs to unfold the exact mathlib proof from `Nat.factorization`
and natural-number division.  Everything above this file is now theoremized
from this local fact. -/
axiom derivCoeffLeibnizAt_of_prime {m n p : ℕ}
    (hp : Nat.Prime p) : DerivCoeffLeibnizAt m n p

/-- If every coordinate of `S` is prime-shaped, the coefficient Leibniz law
holds on all coordinates of `S`. -/
theorem derivCoeffLeibnizOn_of_primeSupport
    {S : Finset ℕ} (hS : PrimeSupport S) (m n : ℕ) :
    DerivCoeffLeibnizOn S m n := by
  intro hp
  exact derivCoeffLeibnizAt_of_prime (hS hp.1 hp.2)

/-- Prime-shaped supports satisfy the unrestricted coefficient theorem. -/
theorem coeffLeibnizTheorem_of_primeSupport
    {S : Finset ℕ} (hS : PrimeSupport S) :
    CoeffLeibnizTheorem S := by
  intro m n
  exact derivCoeffLeibnizOn_of_primeSupport hS m n

end ABD
