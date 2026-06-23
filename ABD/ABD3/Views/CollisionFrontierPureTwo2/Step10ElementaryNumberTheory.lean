import ABD.ABD3.Views.CollisionFrontierPureTwo2.Step9SyncGraph

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo2
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- The A prime is an odd prime in the elementary sense: it is not `2`. -/
theorem p_is_odd_prime_boundary (F : NormalForm T P) :
    Nat.Prime F.p ∧ F.p ≠ 2 :=
  ⟨F.p_prime, F.p_ne_two⟩

/-- The B prime is an odd prime in the elementary sense: it is not `2`. -/
theorem q_is_odd_prime_boundary (F : NormalForm T P) :
    Nat.Prime F.q ∧ F.q ≠ 2 :=
  ⟨F.q_prime, F.q_ne_two⟩

/-- The A base is at least `3`. -/
theorem three_le_p (F : NormalForm T P) :
    3 ≤ F.p := by
  have h2 : 2 ≤ F.p := F.p_prime.two_le
  have hne : F.p ≠ 2 := F.p_ne_two
  omega

/-- The B base is at least `4`; the sharper `5 ≤ q` is kept in the elementary
package below because it uses the primality boundary together with `p < q`. -/
theorem four_le_q (F : NormalForm T P) :
    4 ≤ F.q := by
  have hp3 : 3 ≤ F.p := F.three_le_p
  have hpq : F.p < F.q := F.p_lt_q
  omega

/-- Elementary lower-bound target: sharpen `4 ≤ q` to `5 ≤ q` using primality. -/
def FiveLeQGoal (F : NormalForm T P) : Prop :=
  5 ≤ F.q

/-- Elementary lower-bound target: from `p^u + q^v = 2^w` and `p ≥ 3`, `q ≥ 5`,
deduce `3 ≤ w`. -/
def ThreeLeWGoal (F : NormalForm T P) : Prop :=
  3 ≤ F.w

/-- Mod-8 source equation target.  This is the first clean modular form of
`p^u + q^v = 2^w` once `3 ≤ w` is available. -/
def SourceSumModEightGoal (F : NormalForm T P) : Prop :=
  (F.p ^ F.u + F.q ^ F.v) % 8 = 0

/-- Parity obstruction target: the two exponents cannot both be even. -/
def NotBothExponentsEvenGoal (F : NormalForm T P) : Prop :=
  ¬ (Even F.u ∧ Even F.v)

/-- First mod-8 branch target: if `u` is even and `v` is odd then `q ≡ 7 mod 8`. -/
def EvenUOddVForcesQSevenModEightGoal (F : NormalForm T P) : Prop :=
  Even F.u → ¬ Even F.v → F.q % 8 = 7

/-- Second mod-8 branch target: if `u` is odd and `v` is even then `p ≡ 7 mod 8`. -/
def OddUEvenVForcesPSevenModEightGoal (F : NormalForm T P) : Prop :=
  ¬ Even F.u → Even F.v → F.p % 8 = 7

/-- Third mod-8 branch target: if both exponents are odd then `p + q ≡ 0 mod 8`. -/
def OddUOddVForcesPAddQZeroModEightGoal (F : NormalForm T P) : Prop :=
  ¬ Even F.u → ¬ Even F.v → (F.p + F.q) % 8 = 0

/-- Collected elementary-number-theory layer for the pure two-power model.  This
package is independent of the `{2}` C-surplus identification from Steps 8--9; it
is the remaining parity/mod-8 refinement that can be added to the frontier once
proved. -/
structure ElementaryConstraints (F : NormalForm T P) where
  five_le_q : F.FiveLeQGoal
  three_le_w : F.ThreeLeWGoal
  source_sum_mod_eight : F.SourceSumModEightGoal
  not_both_exponents_even : F.NotBothExponentsEvenGoal
  even_u_odd_v_forces_q_mod8_eq_7 : F.EvenUOddVForcesQSevenModEightGoal
  odd_u_even_v_forces_p_mod8_eq_7 : F.OddUEvenVForcesPSevenModEightGoal
  odd_u_odd_v_forces_p_add_q_mod8_eq_zero : F.OddUOddVForcesPAddQZeroModEightGoal

/-- Remaining elementary target for enriching the final three-rejection frontier
with parity and mod-8 information. -/
def ElementaryConstraintsGoal (F : NormalForm T P) : Prop :=
  Nonempty (ElementaryConstraints F)

/-- An odd square is `1 mod 8`. -/
private theorem odd_sq_mod_eight {x : ℕ} (hx : Odd x) :
    x ^ 2 % 8 = 1 := by
  rcases hx with ⟨k, rfl⟩
  have hEven : Even (k * (k + 1)) := Nat.even_mul_succ_self k
  rcases hEven with ⟨m, hm⟩
  have hsq : (2 * k + 1) ^ 2 = 8 * m + 1 := by
    nlinarith
  rw [hsq]
  simp

/-- Odd base, even exponent: `x^n ≡ 1 mod 8`. -/
private theorem odd_pow_even_exp_mod_eight
    {x n : ℕ} (hx : Odd x) (hn : Even n) :
    x ^ n % 8 = 1 := by
  rcases hn with ⟨k, rfl⟩
  rw [pow_add]
  simpa [pow_two] using odd_sq_mod_eight (hx.pow (n := k))

/-- Odd base, odd exponent: `x^n ≡ x mod 8`. -/
private theorem odd_pow_odd_exp_mod_eight
    {x n : ℕ} (hx : Odd x) (hn : Odd n) :
    x ^ n % 8 = x % 8 := by
  rcases hn with ⟨k, rfl⟩
  have h2k_even : Even (2 * k) := by
    exact ⟨k, Nat.two_mul k⟩
  have heven : x ^ (2 * k) % 8 = 1 :=
    odd_pow_even_exp_mod_eight hx h2k_even
  rw [pow_succ]
  calc
    (x ^ (2 * k) * x) % 8
        = ((x ^ (2 * k) % 8) * (x % 8)) % 8 := by
            rw [Nat.mul_mod]
    _ = (1 * (x % 8)) % 8 := by
            rw [heven]
    _ = x % 8 := by
            simp

/-- A prime different from `2` is odd. -/
theorem odd_of_prime_ne_two {p : ℕ}
    (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    Odd p := by
  rcases hp.eq_two_or_odd with h | h
  · exact False.elim (hp2 h)
  · exact Nat.odd_iff.mpr h

/-- If `(1+x) ≡ 0 mod 8` and `0 ≤ x < 8`, then `x=7`. -/
private theorem mod8_eq_seven_of_one_add_mod8_eq_zero
    {x : ℕ} (hx : x < 8) (h : (1 + x) % 8 = 0) :
    x = 7 := by
  omega

/-- Convert a mod-8 statement about a sum into a statement about residues. -/
private theorem add_mod_eight_zero_of_sum_mod_eight
    {a b : ℕ} (h : (a + b) % 8 = 0) :
    ((a % 8) + (b % 8)) % 8 = 0 := by
  have hrewrite :
      (a + b) % 8 = ((a % 8) + (b % 8)) % 8 := by
    rw [Nat.add_mod]
  rw [← hrewrite]
  exact h

/-- The `SourceSumModEightGoal` form rewritten as the residue-sum form. -/
private theorem residue_sum_mod_eight_of_source_sum_mod_eight
    (F : NormalForm T P)
    (h : F.SourceSumModEightGoal) :
    ((F.p ^ F.u % 8) + (F.q ^ F.v % 8)) % 8 = 0 := by
  have hopen :
      (F.p ^ F.u + F.q ^ F.v) % 8 = 0 := by
    change F.SourceSumModEightGoal
    exact h
  exact add_mod_eight_zero_of_sum_mod_eight hopen

/-- Positive exponent monotonicity in the base: `a ≤ a^n` for `n>0`. -/
theorem self_le_pow_of_pos_exp
    {a n : ℕ} (ha : 0 < a) (hn : 0 < n) :
    a ≤ a ^ n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hn)
  rw [hk, pow_succ']
  have hkpos : 0 < a ^ k := Nat.pow_pos ha
  exact Nat.le_mul_of_pos_right a hkpos

/-- The sharper lower bound `5 ≤ q`. -/
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

/-- If `8 ≤ 2^w`, then `3 ≤ w`. -/
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

/-- From `p ≥ 3`, `q ≥ 5`, positive exponents, and
`p^u+q^v=2^w`, get `3 ≤ w`. -/
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

/-- Once `3 ≤ w`, the source equation is `0 mod 8`. -/
theorem source_sum_mod_eight_real
    (F : NormalForm T P) (hthree : F.ThreeLeWGoal) :
    F.SourceSumModEightGoal := by
  have hdiv : 8 ∣ 2 ^ F.w := by
    change 2 ^ 3 ∣ 2 ^ F.w
    refine ⟨2 ^ (F.w - 3), ?_⟩
    rw [← pow_add, Nat.add_sub_of_le hthree]
  change (F.p ^ F.u + F.q ^ F.v) % 8 = 0
  rw [F.source_sum_eq_two_pow]
  exact Nat.mod_eq_zero_of_dvd hdiv

/-- Mod-8 obstruction: odd bases cannot both have even exponents in
`x^u+y^v ≡ 0 mod 8`. -/
private theorem not_both_even_of_odd_bases_sum_mod_eight
    {x y u v : ℕ}
    (hx : Odd x) (hy : Odd y)
    (hsum : ((x ^ u % 8) + (y ^ v % 8)) % 8 = 0) :
    ¬ (Even u ∧ Even v) := by
  intro hboth
  rcases hboth with ⟨hu_even, hv_even⟩
  have hxmod : x ^ u % 8 = 1 :=
    odd_pow_even_exp_mod_eight hx hu_even
  have hymod : y ^ v % 8 = 1 :=
    odd_pow_even_exp_mod_eight hy hv_even
  have hbad : (1 + 1) % 8 = 0 := by
    simp [hxmod, hymod] at hsum
  exact (by decide : ¬ (1 + 1) % 8 = 0) hbad

/-- If the left exponent is even and the right exponent is odd, the right base is
`7 mod 8`. -/
private theorem even_odd_forces_right_mod8_eq_seven
    {x y u v : ℕ}
    (hx : Odd x) (hy : Odd y)
    (hsum : ((x ^ u % 8) + (y ^ v % 8)) % 8 = 0)
    (hu_even : Even u) (hv_not_even : ¬ Even v) :
    y % 8 = 7 := by
  have hv_odd : Odd v := Nat.not_even_iff_odd.mp hv_not_even
  have hxmod : x ^ u % 8 = 1 :=
    odd_pow_even_exp_mod_eight hx hu_even
  have hymod : y ^ v % 8 = y % 8 :=
    odd_pow_odd_exp_mod_eight hy hv_odd
  have hysum : (1 + y % 8) % 8 = 0 := by
    simpa [hxmod, hymod] using hsum
  exact mod8_eq_seven_of_one_add_mod8_eq_zero
    (Nat.mod_lt y (by decide : 0 < 8)) hysum

/-- If the left exponent is odd and the right exponent is even, the left base is
`7 mod 8`. -/
private theorem odd_even_forces_left_mod8_eq_seven
    {x y u v : ℕ}
    (hx : Odd x) (hy : Odd y)
    (hsum : ((x ^ u % 8) + (y ^ v % 8)) % 8 = 0)
    (hu_not_even : ¬ Even u) (hv_even : Even v) :
    x % 8 = 7 := by
  have hu_odd : Odd u := Nat.not_even_iff_odd.mp hu_not_even
  have hxmod : x ^ u % 8 = x % 8 :=
    odd_pow_odd_exp_mod_eight hx hu_odd
  have hymod : y ^ v % 8 = 1 :=
    odd_pow_even_exp_mod_eight hy hv_even
  have hxsum : (x % 8 + 1) % 8 = 0 := by
    simpa [hxmod, hymod, Nat.add_comm] using hsum
  have hxsum' : (1 + x % 8) % 8 = 0 := by
    simpa [Nat.add_comm] using hxsum
  exact mod8_eq_seven_of_one_add_mod8_eq_zero
    (Nat.mod_lt x (by decide : 0 < 8)) hxsum'

/-- If both exponents are odd, the two bases sum to `0 mod 8`. -/
private theorem odd_odd_forces_base_sum_mod8_zero
    {x y u v : ℕ}
    (hx : Odd x) (hy : Odd y)
    (hsum : ((x ^ u % 8) + (y ^ v % 8)) % 8 = 0)
    (hu_not_even : ¬ Even u) (hv_not_even : ¬ Even v) :
    (x + y) % 8 = 0 := by
  have hu_odd : Odd u := Nat.not_even_iff_odd.mp hu_not_even
  have hv_odd : Odd v := Nat.not_even_iff_odd.mp hv_not_even
  have hxmod : x ^ u % 8 = x % 8 :=
    odd_pow_odd_exp_mod_eight hx hu_odd
  have hymod : y ^ v % 8 = y % 8 :=
    odd_pow_odd_exp_mod_eight hy hv_odd
  have hxysum : (x % 8 + y % 8) % 8 = 0 := by
    simpa [hxmod, hymod] using hsum
  calc
    (x + y) % 8
        = (x % 8 + y % 8) % 8 := by
            rw [Nat.add_mod]
    _ = 0 := hxysum

/-- Realization of the elementary parity/mod-8 package. -/
theorem elementaryConstraints_real (F : NormalForm T P) :
    ElementaryConstraints F := by
  have hp_odd : Odd F.p := odd_of_prime_ne_two F.p_prime F.p_ne_two
  have hq_odd : Odd F.q := odd_of_prime_ne_two F.q_prime F.q_ne_two
  have hfive : F.FiveLeQGoal :=
    F.five_le_q_real
  have hthree : F.ThreeLeWGoal :=
    F.three_le_w_real hfive
  have hmod8 : F.SourceSumModEightGoal :=
    F.source_sum_mod_eight_real hthree
  have hsum8 :
      ((F.p ^ F.u % 8) + (F.q ^ F.v % 8)) % 8 = 0 :=
    residue_sum_mod_eight_of_source_sum_mod_eight F hmod8
  refine
    { five_le_q := hfive
      three_le_w := hthree
      source_sum_mod_eight := hmod8
      not_both_exponents_even := ?_
      even_u_odd_v_forces_q_mod8_eq_7 := ?_
      odd_u_even_v_forces_p_mod8_eq_7 := ?_
      odd_u_odd_v_forces_p_add_q_mod8_eq_zero := ?_ }
  · exact not_both_even_of_odd_bases_sum_mod_eight
      hp_odd hq_odd hsum8
  · intro hu_even hv_not_even
    exact even_odd_forces_right_mod8_eq_seven
      hp_odd hq_odd hsum8 hu_even hv_not_even
  · intro hu_not_even hv_even
    exact odd_even_forces_left_mod8_eq_seven
      hp_odd hq_odd hsum8 hu_not_even hv_even
  · intro hu_not_even hv_not_even
    exact odd_odd_forces_base_sum_mod8_zero
      hp_odd hq_odd hsum8 hu_not_even hv_not_even

/-- The elementary package is now available as a theorem-level target. -/
theorem elementaryConstraintsGoal (F : NormalForm T P) :
    F.ElementaryConstraintsGoal :=
  ⟨F.elementaryConstraints_real⟩

end NormalForm
end CollisionFrontierPureTwo2
end ABCData
end ABD3
