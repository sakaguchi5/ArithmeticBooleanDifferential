import ABD.Memo.QuadraticCyclotomicLift2_Residues
import Mathlib.NumberTheory.Multiplicity

/-
QuadraticCyclotomicLift2_GeneratedZero.lean

Continuation of the p = 7 quadratic-cyclotomic route.

The previous files reduced the generated a = 4 and a = 5 branches to the small
quadratic tests `Phi3` and `Phi6`, after automatically discharging the uXnit
conditions from mod-7 residue data.

This file proves the minimum guaranteed lift produced by the generators:

  A74 r = 4^(7^r)  satisfies  (A74 r)^3 = 1  in ZMod (7^(r+1)),
  A75 r = 5^(7^r)  satisfies  (A75 r)^6 = 1  in ZMod (7^(r+1)).

Equivalently, the generated representatives always pass the naive high-power
zero tests at the guaranteed level.  The proof uses the standard LTE theorem
`padicValNat.pow_sub_pow` in the concrete forms

  v_7(64^(7^r) - 1)     >= r+1,
  v_7(15625^(7^r) - 1)  >= r+1.
-/

namespace QuadraticCyclotomicLift2

/-!
Step 7A.  A small bridge from p-adic valuation/divisibility to zero in
`ZMod (7^(r+1))`.
-/

/-- If `7^(r+1)` divides a natural number, then its cast into `Mod7Step r` is 0. -/
theorem natCast_eq_zero_mod7Step_of_dvd
    (r n : ℕ)
    (h : 7 ^ (r + 1) ∣ n) :
    ((n : ℕ) : Mod7Step r) = 0 := by
  haveI : NeZero (7 ^ (r + 1)) := neZero_mod7Step_modulus r
  exact (ZMod.natCast_eq_zero_iff n (7 ^ (r + 1))).2 h

/-!
Step 7B.  LTE divisibility facts for the two generated branches.
-/

/-- `7^(r+1)` divides `64^(7^r)-1`. -/
theorem seven_pow_succ_dvd_64_pow_sevenPow_sub_one (r : ℕ) :
    7 ^ (r + 1) ∣ 64 ^ (7 ^ r) - 1 := by
  haveI : Fact (Nat.Prime 7) := by decide
  have hval_lte :=
    padicValNat.pow_sub_pow
      (p := 7) (x := 64) (y := 1)
      (by decide : Odd 7)
      (by norm_num : 1 < 64)
      (by norm_num : 7 ∣ 64 - 1)
      (by norm_num : ¬ 7 ∣ 64)
      (n := 7 ^ r)
      (by exact pow_ne_zero r (by norm_num : (7 : ℕ) ≠ 0))
  have hval :
      padicValNat 7 (64 ^ (7 ^ r) - 1) = padicValNat 7 63 + r := by
    simpa [padicValNat.prime_pow] using hval_lte
  have h63ge : 1 ≤ padicValNat 7 63 := by
    exact one_le_padicValNat_of_dvd (by norm_num) (by norm_num)
  have hge : r + 1 ≤ padicValNat 7 (64 ^ (7 ^ r) - 1) := by
    rw [hval]
    have htmp : 1 + r ≤ padicValNat 7 63 + r := Nat.add_le_add_right h63ge r
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htmp
  exact (padicValNat_dvd_iff (p := 7) (n := r + 1) (a := 64 ^ (7 ^ r) - 1)).2
    (Or.inr hge)

/-- `7^(r+1)` divides `15625^(7^r)-1`. -/
theorem seven_pow_succ_dvd_15625_pow_sevenPow_sub_one (r : ℕ) :
    7 ^ (r + 1) ∣ 15625 ^ (7 ^ r) - 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hval_lte :=
    padicValNat.pow_sub_pow
      (p := 7) (x := 15625) (y := 1)
      (by decide : Odd 7)
      (by norm_num : 1 < 15625)
      (by norm_num : 7 ∣ 15625 - 1)
      (by norm_num : ¬ 7 ∣ 15625)
      (n := 7 ^ r)
      (by exact pow_ne_zero r (by norm_num : (7 : ℕ) ≠ 0))
  have hval :
      padicValNat 7 (15625 ^ (7 ^ r) - 1) = padicValNat 7 15624 + r := by
    simpa [padicValNat.prime_pow] using hval_lte
  have h15624ge : 1 ≤ padicValNat 7 15624 := by
    exact one_le_padicValNat_of_dvd (by norm_num) (by norm_num)
  have hge : r + 1 ≤ padicValNat 7 (15625 ^ (7 ^ r) - 1) := by
    rw [hval]
    have htmp : 1 + r ≤ padicValNat 7 15624 + r := Nat.add_le_add_right h15624ge r
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htmp
  exact (padicValNat_dvd_iff (p := 7) (n := r + 1) (a := 15625 ^ (7 ^ r) - 1)).2
    (Or.inr hge)

/-!
Step 7C.  Turn the LTE divisibility facts into zero facts in the one-step-higher
modulus.
-/
/-- Cast helper: `(a : R)^e - 1` is the cast of `a^e - 1`. -/
lemma natCast_pow_sub_one
    {R : Type*} [Ring R]
    (a e : ℕ) (ha : 0 < a) :
    (a : R) ^ e - 1 = ((a ^ e - 1 : ℕ) : R) := by
  have hle : 1 ≤ a ^ e :=
    Nat.succ_le_of_lt (Nat.pow_pos ha)
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one]

lemma pow_sub_one_eq_zero_mod7Step_of_dvd
    (r a e : ℕ) (ha : 0 < a)
    (hdiv : 7 ^ (r + 1) ∣ a ^ e - 1) :
    (a : Mod7Step r) ^ e - 1 = 0 := by
  rw [natCast_pow_sub_one a e ha]
  exact natCast_eq_zero_mod7Step_of_dvd r _ hdiv

theorem pow64_sevenPow_sub_one_eq_zero_mod7Step (r : ℕ) :
    (64 : Mod7Step r) ^ (7 ^ r) - 1 = 0 := by
  exact pow_sub_one_eq_zero_mod7Step_of_dvd r 64 (7 ^ r)
    (by norm_num : 0 < 64)
    (seven_pow_succ_dvd_64_pow_sevenPow_sub_one r)

theorem pow15625_sevenPow_sub_one_eq_zero_mod7Step (r : ℕ) :
    (15625 : Mod7Step r) ^ (7 ^ r) - 1 = 0 := by
  exact pow_sub_one_eq_zero_mod7Step_of_dvd r 15625 (7 ^ r)
    (by norm_num : 0 < 15625)
    (seven_pow_succ_dvd_15625_pow_sevenPow_sub_one r)

/-!
Step 7D.  The generated representatives pass the naive high-power tests.
-/

/-- Generated a = 4 branch: the naive cubic test always holds at level `7^(r+1)`. -/
theorem A74_cubic_naive_test_holds (r : ℕ) :
    CubicNaiveTest r (A74 r) := by
  exact (A74_cubic_test_lte_form r).2
    (pow64_sevenPow_sub_one_eq_zero_mod7Step r)

/-- Generated a = 5 branch: the naive sixth-power test always holds at level `7^(r+1)`. -/
theorem A75_sixth_naive_test_holds (r : ℕ) :
    SixthNaiveTest r (A75 r) := by
  exact (A75_sixth_test_lte_form r).2
    (pow15625_sevenPow_sub_one_eq_zero_mod7Step r)

/-!
Step 7E.  Combining this file with the quadratic reduction: the generated
branches always pass the small quadratic tests at the guaranteed level.
-/

/-- Generated a = 4 branch: `Phi3(A74 r)` is zero in `ZMod (7^(r+1))`. -/
theorem A74_phi3_test_holds (r : ℕ) :
    Phi3Test r (A74 r) := by
  exact (a4_generated_quadratic_test_correct_auto r).1
    (A74_cubic_naive_test_holds r)

/-- Generated a = 5 branch: `Phi6(A75 r)` is zero in `ZMod (7^(r+1))`. -/
theorem A75_phi6_test_holds (r : ℕ) :
    Phi6Test r (A75 r) := by
  exact (a5_generated_quadratic_test_correct_auto r).1
    (A75_sixth_naive_test_holds r)

end QuadraticCyclotomicLift2
