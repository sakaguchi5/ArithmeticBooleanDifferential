import Mathlib.Algebra.Ring.GeomSum
import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step6ModEightConstraints

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- For odd `n`, `X+Y` divides `X^n+Y^n`.

This is the divisibility part of the odd-power factorization, obtained from
`x^n - y^n` by substituting `y := -Y` over `ℤ`. -/
theorem add_dvd_pow_add_pow_of_odd
    {X Y n : ℕ} (hn : Odd n) :
    X + Y ∣ X ^ n + Y ^ n := by
  have hsub :
      ((X : ℤ) - (-(Y : ℤ))) ∣
        (X : ℤ) ^ n - (-(Y : ℤ)) ^ n :=
    (Commute.all (X : ℤ) (-(Y : ℤ))).sub_dvd_pow_sub_pow n
  have hneg : (-(Y : ℤ)) ^ n = -((Y : ℤ) ^ n) :=
    hn.neg_pow (Y : ℤ)
  have hsub' :
      ((X : ℤ) + (Y : ℤ)) ∣
        (X : ℤ) ^ n + (Y : ℤ) ^ n := by
    simpa [sub_eq_add_neg, hneg] using hsub
  have hcast :
      (((X + Y : ℕ) : ℤ)) ∣
        (((X ^ n + Y ^ n : ℕ) : ℤ)) := by
    simpa [Nat.cast_add, Nat.cast_pow] using hsub'
  exact Int.natCast_dvd_natCast.mp hcast

/-- If `S = A*Q` and `S` is strictly larger than `A`, then the quotient is
larger than `1`. -/
theorem quotient_gt_one_of_factor_gt
    {A S Q : ℕ}
    (hfactor : S = A * Q)
    (hgt : A < S) :
    1 < Q := by
  by_contra hnot
  have hQle : Q ≤ 1 := Nat.le_of_not_gt hnot
  have hAQle : A * Q ≤ A * 1 :=
    Nat.mul_le_mul_left A hQle
  have hSle : S ≤ A := by
    calc
      S = A * Q := hfactor
      _ ≤ A * 1 := hAQle
      _ = A := by rw [Nat.mul_one]
  exact not_lt_of_ge hSle hgt

/-- If `1 < a` and `2 ≤ n`, then `a < a^n`. -/
theorem lt_pow_of_one_lt_of_two_le
    {a n : ℕ} (ha : 1 < a) (hn : 2 ≤ n) :
    a < a ^ n := by
  have ha_pos : 0 < a :=
    Nat.lt_trans Nat.zero_lt_one ha
  have hsq : a < a ^ 2 := by
    rw [pow_two]
    nlinarith
  have hmono : a ^ 2 ≤ a ^ n :=
    pow_le_pow_right' (Nat.succ_le_of_lt ha_pos) hn
  exact lt_of_lt_of_le hsq hmono

/-- Nat-level wrapper for the binomial quotient parity.

If `A` is even, `Y` is odd, `n` is odd, `Y ≤ A`, and

`(A - Y)^n + Y^n = A * R`,

then `R` is odd. -/
theorem odd_binomial_quotient_nat
    {A Y n R : ℕ}
    (hA_even : Even A)
    (hY_odd : Odd Y)
    (hn_odd : Odd n)
    (hY_le_A : Y ≤ A)
    (hfactor : (A - Y) ^ n + Y ^ n = A * R) :
    Odd R := by
  let X : ℕ := A - Y
  have hX_add_Y : X + Y = A := by
    dsimp [X]
    exact Nat.sub_add_cancel hY_le_A
  have hA_pos : 0 < A := by
    have hY_pos : 0 < Y := pos_of_odd_nat hY_odd
    exact lt_of_lt_of_le hY_pos hY_le_A
  have hX_odd : Odd X := by
    by_contra hnot
    have hX_even : Even X := Nat.not_odd_iff_even.mp hnot
    have hsum_odd : Odd (X + Y) := by
      rcases hX_even with ⟨a, ha⟩
      rcases hY_odd with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      rw [ha, hb]
      omega
    have hA_odd : Odd A := by
      rw [← hX_add_Y]
      exact hsum_odd
    exact odd_not_even_nat hA_odd hA_even
  have hmod_sum :
      (X ^ n + Y ^ n) % (2 * (X + Y)) = X + Y :=
    odd_pow_sum_mod_two_mul_sum hX_odd hY_odd hn_odd
  have hmod_A :
      (A * R) % (2 * A) = A := by
    rw [← hfactor]
    dsimp [X] at hmod_sum
    simpa [Nat.sub_add_cancel hY_le_A] using hmod_sum
  by_contra hR_not_odd
  have hR_even : Even R :=
    Nat.not_odd_iff_even.mp hR_not_odd
  rcases hR_even with ⟨k, hk⟩
  have hmod_even : (A * R) % (2 * A) = 0 := by
    rw [hk]
    have hrewrite : A * (k + k) = (2 * A) * k := by
      nlinarith
    rw [hrewrite]
    exact Nat.mul_mod_right (2 * A) k
  rw [hmod_even] at hmod_A
  have hzero_ne_A : (0 : ℕ) ≠ A :=
    Nat.ne_of_lt hA_pos
  exact hzero_ne_A hmod_A

/-- The quotient in `X^n+Y^n=(X+Y)Q` is odd. -/
theorem odd_quotient_of_odd_add_pow_factor
    {X Y n Q : ℕ}
    (hX_odd : Odd X) (hY_odd : Odd Y) (hn_odd : Odd n)
    (hfactor : X ^ n + Y ^ n = (X + Y) * Q) :
    Odd Q := by
  let A : ℕ := X + Y
  have hA_even : Even A := by
    dsimp [A]
    rcases hX_odd with ⟨a, ha⟩
    rcases hY_odd with ⟨b, hb⟩
    refine ⟨a + b + 1, ?_⟩
    rw [ha, hb]
    omega
  have hY_le_A : Y ≤ A := by
    dsimp [A]
    exact Nat.le_add_left Y X
  have hA_sub_Y : A - Y = X := by
    dsimp [A]
    omega
  have hfactorA : (A - Y) ^ n + Y ^ n = A * Q := by
    rw [hA_sub_Y]
    dsimp [A]
    exact hfactor
  exact odd_binomial_quotient_nat
    hA_even hY_odd hn_odd hY_le_A hfactorA

/-- Standard algebraic factorization input.

For odd prime `ℓ`, if `X,Y` are odd and both greater than `1`, then
`X^ℓ + Y^ℓ` has a nontrivial odd quotient after dividing by `X+Y`. -/
theorem odd_prime_add_pow_factor_has_odd_gt_one_quotient
    {X Y ℓ : ℕ}
    (hX_odd : Odd X) (hY_odd : Odd Y)
    (hX_gt_one : 1 < X) (hY_gt_one : 1 < Y)
    (hℓ_prime : Nat.Prime ℓ) (hℓ_ne_two : ℓ ≠ 2) :
    ∃ Q : ℕ,
      X ^ ℓ + Y ^ ℓ = (X + Y) * Q ∧ Odd Q ∧ 1 < Q := by
  have hℓ_odd : Odd ℓ :=
    odd_of_prime_ne_two hℓ_prime hℓ_ne_two
  have hdiv : X + Y ∣ X ^ ℓ + Y ^ ℓ :=
    add_dvd_pow_add_pow_of_odd hℓ_odd
  let Q : ℕ := (X ^ ℓ + Y ^ ℓ) / (X + Y)
  have hQeq : X ^ ℓ + Y ^ ℓ = (X + Y) * Q := by
    dsimp [Q]
    rw [Nat.mul_comm]
    exact (Nat.div_mul_cancel hdiv).symm
  have hQodd : Odd Q :=
    odd_quotient_of_odd_add_pow_factor hX_odd hY_odd hℓ_odd hQeq
  have hℓ_three : 3 ≤ ℓ := by
    have htwo : 2 ≤ ℓ := hℓ_prime.two_le
    omega
  have hℓ_two : 2 ≤ ℓ := by
    exact le_trans (by decide : 2 ≤ 3) hℓ_three
  have hX_lt_pow : X < X ^ ℓ :=
    lt_pow_of_one_lt_of_two_le hX_gt_one hℓ_two
  have hY_lt_pow : Y < Y ^ ℓ :=
    lt_pow_of_one_lt_of_two_le hY_gt_one hℓ_two
  have hsum_gt : X + Y < X ^ ℓ + Y ^ ℓ :=
    Nat.add_lt_add hX_lt_pow hY_lt_pow
  have hQgt : 1 < Q :=
    quotient_gt_one_of_factor_gt hQeq hsum_gt
  exact ⟨Q, hQeq, hQodd, hQgt⟩

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
