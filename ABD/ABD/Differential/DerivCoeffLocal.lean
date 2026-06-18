import ABD.ABD.Core.ValuationLemmas
import ABD.ABD.Differential.LeibnizCoeff

namespace ABD

private theorem int_mul_rotate (a b c : ℤ) :
    a * (b * c) = b * (a * c) := by
  exact mul_left_comm a b c

private theorem int_add_mul_swap (a b c : ℤ) :
    (a + b) * c = b * c + a * c := by
  rw [add_mul, add_comm]

/-- Local multiplicativity target for the valuation layer. -/
def ValMulAt (m n p : ℕ) : Prop :=
  val (m * n) p = val m p + val n p

/-- Local coefficient Leibniz target, explicitly named as the arithmetic core of
`DerivCoeffLeibnizAt`.

Mathematically this follows from `ValMulAt` together with the elementary
natural-number division identities for `(m*n)/p`.  It is kept as a separate
name so the raw `Nat.factorization` proof remains local to this file and does
not leak into the higher Pasten wiring. -/
def DerivCoeffLocalLaw (m n p : ℕ) : Prop :=
  DerivCoeffLeibnizAt m n p

@[simp] theorem derivCoeffLocalLaw_iff (m n p : ℕ) :
    DerivCoeffLocalLaw m n p ↔ DerivCoeffLeibnizAt m n p := by
  rfl

/-- If `p` does not divide `n`, the `p`-direction coefficient of `n` vanishes. -/
theorem derivCoeff_eq_zero_of_not_dvd {n p : ℕ} (h : ¬ p ∣ n) :
    derivCoeff n p = 0 := by
  unfold derivCoeff
  rw [val_eq_zero_of_not_dvd h]
  simp

/-- Scaling the `n`-coefficient by `m` rewrites to the common coefficient of
`m*n`, provided `p ∣ n`. -/
theorem int_mul_derivCoeff_eq_val_mul_mul_div_of_dvd_right
    {m n p : ℕ} (hpn : p ∣ n) :
    (m : ℤ) * derivCoeff n p =
      (val n p : ℤ) * (((m * n) / p : ℕ) : ℤ) := by
  unfold derivCoeff
  rw [Nat.mul_div_assoc m hpn]
  rw [Nat.cast_mul]
  exact int_mul_rotate (m : ℤ) (val n p : ℤ) (((n / p : ℕ) : ℤ))

/-- Scaling the `m`-coefficient by `n` rewrites to the common coefficient of
`m*n`, provided `p ∣ m`. -/
theorem int_mul_derivCoeff_eq_val_mul_mul_div_of_dvd_left
    {m n p : ℕ} (hpm : p ∣ m) :
    (n : ℤ) * derivCoeff m p =
      (val m p : ℤ) * (((m * n) / p : ℕ) : ℤ) := by
  unfold derivCoeff
  have hdiv : (m * n) / p = n * (m / p) := by
    rw [Nat.mul_comm m n]
    exact Nat.mul_div_assoc n hpm
  rw [hdiv]
  rw [Nat.cast_mul]
  exact int_mul_rotate (n : ℤ) (val m p : ℤ) (((m / p : ℕ) : ℤ))

/-- For nonzero factors, the derivative coefficient of a product has the
expected valuation-expanded form. -/
theorem derivCoeff_mul_eq_val_add_mul_div
    {m n p : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    derivCoeff (m * n) p =
      ((val m p : ℤ) + (val n p : ℤ)) * (((m * n) / p : ℕ) : ℤ) := by
  unfold derivCoeff
  rw [val_mul_of_ne_zero hm hn]
  rw [Nat.cast_add]

/-- The prime-direction local coefficient Leibniz theorem.

This theorem closes the former arithmetic choke point.  The proof is local:
`Nat.factorization_mul` supplies additivity of valuations for nonzero products,
while `Nat.mul_div_assoc` rewrites the natural-number division part whenever
one factor is divisible by the chosen prime direction. -/
theorem derivCoeffLeibnizAt_of_prime {m n p : ℕ}
    (_hp : Nat.Prime p) : DerivCoeffLeibnizAt m n p := by
  by_cases hm0 : m = 0
  · subst m
    simp [DerivCoeffLeibnizAt, derivCoeff, val]
  by_cases hn0 : n = 0
  · subst n
    simp [DerivCoeffLeibnizAt, derivCoeff, val]
  unfold DerivCoeffLeibnizAt
  rw [derivCoeff_mul_eq_val_add_mul_div hm0 hn0]
  by_cases hpm : p ∣ m
  · by_cases hpn : p ∣ n
    · rw [int_mul_derivCoeff_eq_val_mul_mul_div_of_dvd_right hpn]
      rw [int_mul_derivCoeff_eq_val_mul_mul_div_of_dvd_left hpm]
      simp [add_mul, add_comm]
    · rw [derivCoeff_eq_zero_of_not_dvd hpn]
      rw [val_eq_zero_of_not_dvd hpn]
      rw [int_mul_derivCoeff_eq_val_mul_mul_div_of_dvd_left hpm]
      simp
  · by_cases hpn : p ∣ n
    · rw [derivCoeff_eq_zero_of_not_dvd hpm]
      rw [val_eq_zero_of_not_dvd hpm]
      rw [int_mul_derivCoeff_eq_val_mul_mul_div_of_dvd_right hpn]
      simp
    · rw [derivCoeff_eq_zero_of_not_dvd hpm]
      rw [derivCoeff_eq_zero_of_not_dvd hpn]
      rw [val_eq_zero_of_not_dvd hpm]
      rw [val_eq_zero_of_not_dvd hpn]
      simp

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
