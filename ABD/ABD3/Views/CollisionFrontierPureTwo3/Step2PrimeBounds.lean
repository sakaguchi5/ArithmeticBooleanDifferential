import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step1NormalForm

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Basic power monotonicity for positive bases and positive exponents. -/
theorem self_le_pow_of_pos_exp
    {a n : ℕ} (ha : 0 < a) (hn : 0 < n) :
    a ≤ a ^ n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hn)
  rw [hk, pow_succ']
  have hkpos : 0 < a ^ k := Nat.pow_pos ha
  exact Nat.le_mul_of_pos_right a hkpos

/-- The A base is at least `3`. -/
theorem three_le_p (F : NormalForm T P) :
    3 ≤ F.p := by
  have h2 : 2 ≤ F.p := F.p_prime.two_le
  have hne : F.p ≠ 2 := F.p_ne_two
  omega

/-- The B base is at least `4`; the sharper `5 ≤ q` uses primality below. -/
theorem four_le_q (F : NormalForm T P) :
    4 ≤ F.q := by
  have hp3 : 3 ≤ F.p := F.three_le_p
  have hpq : F.p < F.q := F.p_lt_q
  omega

/-- Lower-bound target: sharpen `4 ≤ q` to `5 ≤ q` using primality. -/
def FiveLeQGoal (F : NormalForm T P) : Prop :=
  5 ≤ F.q

/-- Lower-bound target: from `p^u + q^v = 2^w`, deduce `3 ≤ w`. -/
def ThreeLeWGoal (F : NormalForm T P) : Prop :=
  3 ≤ F.w

/-- Real proof of `5 ≤ q`. -/
theorem five_le_q_real (F : NormalForm T P) :
    F.FiveLeQGoal := by
  have hq_ne_four : F.q ≠ 4 := by
    intro hq4
    have hdiv : 2 ∣ F.q := by
      rw [hq4]
      exact ⟨2, rfl⟩
    have hq_eq_two : 2 = F.q :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_two F.q_prime).mp hdiv
    exact F.q_ne_two hq_eq_two.symm
  exact Nat.succ_le_of_lt
    (lt_of_le_of_ne F.four_le_q hq_ne_four.symm)

private theorem three_le_of_eight_le_two_pow
    {w : ℕ} (h : 8 ≤ 2 ^ w) :
    3 ≤ w := by
  by_contra hnot
  have hw_lt : w < 3 := Nat.lt_of_not_ge hnot
  have hw_le : w ≤ 2 := Nat.le_of_lt_succ hw_lt
  have hpow_le : 2 ^ w ≤ 2 ^ 2 :=
    pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hw_le
  have hbad : 8 ≤ 4 := by
    calc
      8 ≤ 2 ^ w := h
      _ ≤ 2 ^ 2 := hpow_le
      _ = 4 := rfl
  exact (by decide : ¬ 8 ≤ 4) hbad

/-- Real proof of `3 ≤ w`. -/
theorem three_le_w_real
    (F : NormalForm T P) (hfive : F.FiveLeQGoal) :
    F.ThreeLeWGoal := by
  have hp_le_pow : F.p ≤ F.p ^ F.u :=
    self_le_pow_of_pos_exp F.p_pos F.u_pos
  have hq_le_pow : F.q ≤ F.q ^ F.v :=
    self_le_pow_of_pos_exp F.q_pos F.v_pos
  have hp_pow_ge : 3 ≤ F.p ^ F.u :=
    le_trans F.three_le_p hp_le_pow
  have hq_pow_ge : 5 ≤ F.q ^ F.v :=
    le_trans hfive hq_le_pow
  have hsum_ge : 8 ≤ F.p ^ F.u + F.q ^ F.v := by
    calc
      8 = 3 + 5 := rfl
      _ ≤ F.p ^ F.u + F.q ^ F.v :=
        Nat.add_le_add hp_pow_ge hq_pow_ge
  have hpow_ge : 8 ≤ 2 ^ F.w := by
    calc
      8 ≤ F.p ^ F.u + F.q ^ F.v := hsum_ge
      _ = 2 ^ F.w := F.source_sum_eq_two_pow
  exact three_le_of_eight_le_two_pow hpow_ge

/-- Basic lower-bound package, separated from residue constraints. -/
structure BasicBounds (F : NormalForm T P) where
  five_le_q : F.FiveLeQGoal
  three_le_w : F.ThreeLeWGoal

def BasicBoundsGoal (F : NormalForm T P) : Prop :=
  Nonempty (BasicBounds F)

/-- Realization of the basic bounds. -/
theorem basicBounds_real (F : NormalForm T P) :
    BasicBounds F := by
  have hfive : F.FiveLeQGoal := F.five_le_q_real
  have hthree : F.ThreeLeWGoal := F.three_le_w_real hfive
  exact { five_le_q := hfive, three_le_w := hthree }

theorem basicBoundsGoal (F : NormalForm T P) :
    F.BasicBoundsGoal :=
  ⟨F.basicBounds_real⟩

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
