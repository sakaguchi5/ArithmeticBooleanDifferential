import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step7OddAddPowFactor

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Exponent-coprime target for the pure two-power frontier. -/
def ExponentCoprimeGoal (F : NormalForm T P) : Prop :=
  Nat.Coprime F.u F.v

/-- A common divisor `2 | u,v` contradicts the mod-8 obstruction. -/
theorem two_not_common_exponent_divisor
    (F : NormalForm T P) :
    ¬ (2 ∣ F.u ∧ 2 ∣ F.v) := by
  intro h
  rcases h with ⟨hu2, hv2⟩
  have hu_even : Even F.u := even_of_two_dvd hu2
  have hv_even : Even F.v := even_of_two_dvd hv2
  have H8 : ModEightConstraints F := F.modEightConstraints_real
  exact H8.not_both_exponents_even ⟨hu_even, hv_even⟩

/-- Odd common prime exponent obstruction. -/
theorem odd_prime_not_common_exponent_divisor
    (F : NormalForm T P)
    {ℓ : ℕ} (hℓ_prime : Nat.Prime ℓ) (hℓ_ne_two : ℓ ≠ 2) :
    ¬ (ℓ ∣ F.u ∧ ℓ ∣ F.v) := by
  intro hcommon
  rcases hcommon with ⟨hu_dvd, hv_dvd⟩
  rcases hu_dvd with ⟨u', hu'⟩
  rcases hv_dvd with ⟨v', hv'⟩
  let X : ℕ := F.p ^ u'
  let Y : ℕ := F.q ^ v'
  have hX_odd : Odd X := by
    dsimp [X]
    exact (show Odd (F.p ^ u') from F.p_odd.pow)
  have hY_odd : Odd Y := by
    dsimp [Y]
    exact (show Odd (F.q ^ v') from F.q_odd.pow)
  have hsourceXY : X ^ ℓ + Y ^ ℓ = 2 ^ F.w := by
    dsimp [X, Y]
    calc
      (F.p ^ u') ^ ℓ + (F.q ^ v') ^ ℓ
          = F.p ^ (u' * ℓ) + F.q ^ (v' * ℓ) := by
              rw [pow_mul, pow_mul]
      _ = F.p ^ F.u + F.q ^ F.v := by
              rw [hu', hv']
              rw [Nat.mul_comm u' ℓ, Nat.mul_comm v' ℓ]
      _ = 2 ^ F.w := F.source_sum_eq_two_pow
  have hu'_pos : 0 < u' := by
    by_contra hnot
    have hu0 : u' = 0 := Nat.eq_zero_of_not_pos hnot
    have hu_zero : F.u = 0 := by
      rw [hu', hu0, Nat.mul_zero]
    exact (Nat.ne_of_gt F.u_pos) hu_zero
  have hv'_pos : 0 < v' := by
    by_contra hnot
    have hv0 : v' = 0 := Nat.eq_zero_of_not_pos hnot
    have hv_zero : F.v = 0 := by
      rw [hv', hv0, Nat.mul_zero]
    exact (Nat.ne_of_gt F.v_pos) hv_zero
  have hX_gt_one : 1 < X := by
    dsimp [X]
    have hp_le_pow : F.p ≤ F.p ^ u' :=
      self_le_pow_of_pos_exp F.p_pos hu'_pos
    exact lt_of_lt_of_le
      (by decide : 1 < 3)
      (le_trans F.three_le_p hp_le_pow)
  have hY_gt_one : 1 < Y := by
    dsimp [Y]
    have hq_le_pow : F.q ≤ F.q ^ v' :=
      self_le_pow_of_pos_exp F.q_pos hv'_pos
    exact lt_of_lt_of_le
      (by decide : 1 < 5)
      (le_trans F.five_le_q_real hq_le_pow)
  have hfactor :
      ∃ Q : ℕ,
        X ^ ℓ + Y ^ ℓ = (X + Y) * Q ∧ Odd Q ∧ 1 < Q :=
    odd_prime_add_pow_factor_has_odd_gt_one_quotient
      hX_odd hY_odd hX_gt_one hY_gt_one hℓ_prime hℓ_ne_two
  rcases hfactor with ⟨Q, hQeq, hQodd, hQgt⟩
  have hQ_dvd_two_pow : Q ∣ 2 ^ F.w := by
    refine ⟨X + Y, ?_⟩
    rw [← hsourceXY, hQeq, Nat.mul_comm]
  have hQeq_one : Q = 1 :=
    odd_dvd_two_pow_eq_one hQodd hQ_dvd_two_pow
  exact (Nat.ne_of_gt hQgt) hQeq_one

/-- No prime can divide both exponents in the pure two-power model. -/
theorem no_common_prime_exponent_divisor
    (F : NormalForm T P)
    {ℓ : ℕ} (hℓ_prime : Nat.Prime ℓ) :
    ¬ (ℓ ∣ F.u ∧ ℓ ∣ F.v) := by
  by_cases hℓ2 : ℓ = 2
  · subst ℓ
    exact two_not_common_exponent_divisor F
  · exact odd_prime_not_common_exponent_divisor F hℓ_prime hℓ2

/-- Realization of exponent coprimality in the pure two-power model. -/
theorem exponentCoprime (F : NormalForm T P) :
    F.ExponentCoprimeGoal := by
  rw [ExponentCoprimeGoal]
  change Nat.gcd F.u F.v = 1
  by_contra hgcd_ne_one
  obtain ⟨ℓ, hℓ_prime, hℓ_dvd_gcd⟩ :=
    Nat.exists_prime_and_dvd hgcd_ne_one
  have hℓ_dvd_u : ℓ ∣ F.u :=
    dvd_trans hℓ_dvd_gcd (Nat.gcd_dvd_left F.u F.v)
  have hℓ_dvd_v : ℓ ∣ F.v :=
    dvd_trans hℓ_dvd_gcd (Nat.gcd_dvd_right F.u F.v)
  exact no_common_prime_exponent_divisor F hℓ_prime
    ⟨hℓ_dvd_u, hℓ_dvd_v⟩

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
