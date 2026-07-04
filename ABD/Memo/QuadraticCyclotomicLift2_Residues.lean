import ABD.Memo.QuadraticCyclotomicLift2_UnitAuto
import Mathlib.Tactic.NormNum

/-
QuadraticCyclotomicLift2_Residues.lean

Continuation of the p = 7 quadratic-cyclotomic route.

This file proves the tiny residue facts needed by the unit-free generated
p = 7, a = 4/5 branches.
-/

namespace QuadraticCyclotomicLift2

/-!
Step 6A.  Small natural-number residue cycles modulo 7.
-/

/-- The seed `4` is fixed by the seventh power modulo 7. -/
theorem four_pow_seven_mod7 :
    4 ^ 7 % 7 = 4 := by
  norm_num

/-- The seed `5` is fixed by the seventh power modulo 7. -/
theorem five_pow_seven_mod7 :
    5 ^ 7 % 7 = 5 := by
  norm_num

/-- If `a` has residue `c` modulo 7 and `c` is fixed by seventh power,
then `a^(7^r)` has residue `c` modulo 7 for all `r`. -/
lemma pow_sevenPow_mod7_of_fixed
    (a c r : ℕ)
    (h0 : a % 7 = c)
    (h7 : c ^ 7 % 7 = c) :
    a ^ (7 ^ r) % 7 = c := by
  induction r with
  | zero =>
      simpa using h0
  | succ r ih =>
      calc
        a ^ (7 ^ (r + 1)) % 7
            = ((a ^ (7 ^ r)) ^ 7) % 7 := by
                rw [Nat.pow_succ, pow_mul]
        _ = (((a ^ (7 ^ r)) % 7) ^ 7) % 7 := by
                rw [Nat.pow_mod]
        _ = c ^ 7 % 7 := by
                rw [ih]
        _ = c := h7

/-- For all `r`, `4^(7^r) ≡ 4 mod 7`. -/
theorem four_pow_sevenPow_mod7 (r : ℕ) :
    4 ^ (7 ^ r) % 7 = 4 := by
  exact pow_sevenPow_mod7_of_fixed 4 4 r (by norm_num) four_pow_seven_mod7

/-- For all `r`, `5^(7^r) ≡ 5 mod 7`. -/
theorem five_pow_sevenPow_mod7 (r : ℕ) :
    5 ^ (7 ^ r) % 7 = 5 := by
  exact pow_sevenPow_mod7_of_fixed 5 5 r (by norm_num) five_pow_seven_mod7

/-- A small helper for subtracting one modulo 7. -/
lemma sub_one_mod7_of_mod7_eq
    {n c d : ℕ}
    (hn : n % 7 = c)
    (hd : (c + 7 - 1) % 7 = d)
    (hle : 1 ≤ n) :
    (n - 1) % 7 = d := by
  have hmod :
      (n - 1) % 7 = (n % 7 + 7 - 1) % 7 := by
    omega
  rw [hmod, hn]
  exact hd

/-- A small helper for adding one modulo 7. -/
lemma add_one_mod7_of_mod7_eq
    {n c d : ℕ}
    (hn : n % 7 = c)
    (hd : (c + 1) % 7 = d) :
    (n + 1) % 7 = d := by
  calc
    (n + 1) % 7
        = (n % 7 + 1 % 7) % 7 := by
            rw [Nat.add_mod]
    _ = (c + 1) % 7 := by
            rw [hn]
    _ = d := hd

/-- A small helper for `n^2+n+1` modulo 7. -/
lemma phi3_nat_mod7_of_mod7_eq
    {n c d : ℕ}
    (hn : n % 7 = c)
    (hd : (c ^ 2 + c + 1) % 7 = d) :
    (n ^ 2 + n + 1) % 7 = d := by
  calc
    (n ^ 2 + n + 1) % 7
        = ((n % 7) ^ 2 + n % 7 + 1) % 7 := by
            simp [Nat.add_mod, Nat.pow_mod]
    _ = (c ^ 2 + c + 1) % 7 := by
            rw [hn]
    _ = d := hd

/-- Therefore `4^(7^r)-1` has residue `3` modulo 7. -/
theorem four_pow_sevenPow_sub_one_mod7 (r : ℕ) :
    (4 ^ (7 ^ r) - 1) % 7 = 3 := by
  exact sub_one_mod7_of_mod7_eq
    (four_pow_sevenPow_mod7 r)
    (by norm_num)
    (Nat.succ_le_of_lt (Nat.pow_pos (by norm_num : 0 < 4)))

/-- Therefore `5^(7^r)-1` has residue `4` modulo 7. -/
theorem five_pow_sevenPow_sub_one_mod7 (r : ℕ) :
    (5 ^ (7 ^ r) - 1) % 7 = 4 := by
  exact sub_one_mod7_of_mod7_eq
    (five_pow_sevenPow_mod7 r)
    (by norm_num)
    (Nat.succ_le_of_lt (Nat.pow_pos (by norm_num : 0 < 5)))

/-- Therefore `5^(7^r)+1` has residue `6` modulo 7. -/
theorem five_pow_sevenPow_add_one_mod7 (r : ℕ) :
    (5 ^ (7 ^ r) + 1) % 7 = 6 := by
  exact add_one_mod7_of_mod7_eq
    (five_pow_sevenPow_mod7 r)
    (by norm_num)

/-- Therefore `Phi3(5^(7^r))` has residue `3` modulo 7. -/
theorem phi3_five_pow_sevenPow_mod7 (r : ℕ) :
    ((5 ^ (7 ^ r)) ^ 2 + 5 ^ (7 ^ r) + 1) % 7 = 3 := by
  exact phi3_nat_mod7_of_mod7_eq
    (five_pow_sevenPow_mod7 r)
    (by norm_num)

/-!
Step 6B.  Reducing a cast into `ZMod (7^(r+1))` back modulo 7.
-/

/-- Reducing a representative first modulo `7^(r+1)` and then modulo `7` is the
same as reducing directly modulo `7`. -/
theorem mod7_of_mod7Step_val (r n : ℕ) :
    (n % (7 ^ (r + 1))) % 7 = n % 7 := by
  have hdiv : 7 ∣ 7 ^ (r + 1) := by
    have h : 7 ^ (r + 1) = 7 * 7 ^ r := by
      ring
    exact ⟨7 ^ r, by
      simpa [mul_comm]⟩
  exact Nat.mod_mod_of_dvd n hdiv

/-- The value of a natural cast into `Mod7Step r`, reduced again modulo 7. -/
theorem natCast_val_mod7Step_mod7 (r n : ℕ) :
    (((n : Mod7Step r).val) % 7) = n % 7 := by
  haveI : NeZero (7 ^ (r + 1)) := neZero_mod7Step_modulus r
  rw [ZMod.val_natCast]
  exact mod7_of_mod7Step_val r n

/-!
Step 6C.  Generated residue facts in `ZMod (7^(r+1))`.
-/

/-- Expand the generated `a = 4` minus-one factor as a natural cast. -/
lemma A74_minus_one_eq_natCast (r : ℕ) :
    (A74 r - 1 : Mod7Step r)
      =
    ((4 ^ (7 ^ r) - 1 : ℕ) : Mod7Step r) := by
  have hle : 1 ≤ 4 ^ (7 ^ r) := by
    exact Nat.succ_le_of_lt (Nat.pow_pos (by norm_num : 0 < 4))
  unfold A74
  rw [Nat.cast_sub hle]
  rw [Nat.cast_pow]
  norm_num

/-- Expand the generated `a = 5` minus-one factor as a natural cast. -/
lemma A75_minus_one_eq_natCast (r : ℕ) :
    (A75 r - 1 : Mod7Step r)
      =
    ((5 ^ (7 ^ r) - 1 : ℕ) : Mod7Step r) := by
  have hle : 1 ≤ 5 ^ (7 ^ r) := by
    exact Nat.succ_le_of_lt (Nat.pow_pos (by norm_num : 0 < 5))
  unfold A75
  rw [Nat.cast_sub hle]
  rw [Nat.cast_pow]
  norm_num

/-- Expand the generated `a = 5` plus-one factor as a natural cast. -/
lemma A75_plus_one_eq_natCast (r : ℕ) :
    (A75 r + 1 : Mod7Step r)
      =
    ((5 ^ (7 ^ r) + 1 : ℕ) : Mod7Step r) := by
  unfold A75
  rw [Nat.cast_add, Nat.cast_pow]
  norm_num

/-- Expand the generated `Phi3(A75 r)` factor as a natural cast. -/
lemma Phi3_A75_eq_natCast (r : ℕ) :
    Phi3 (A75 r)
      =
    ((((5 ^ (7 ^ r)) ^ 2 + 5 ^ (7 ^ r) + 1 : ℕ) : Mod7Step r)) := by
  unfold A75 Phi3
  norm_num [Nat.cast_add, Nat.cast_pow]

/-- The generated a = 4 non-target factor has residue `3` modulo 7. -/
theorem A74_minus_one_val_mod7 (r : ℕ) :
    (A74 r - 1).val % 7 = 3 := by
  rw [A74_minus_one_eq_natCast r]
  rw [natCast_val_mod7Step_mod7 r]
  exact four_pow_sevenPow_sub_one_mod7 r

/-- The generated a = 5 non-target factor has residue `4` modulo 7. -/
theorem A75_minus_one_val_mod7 (r : ℕ) :
    (A75 r - 1).val % 7 = 4 := by
  rw [A75_minus_one_eq_natCast r]
  rw [natCast_val_mod7Step_mod7 r]
  exact five_pow_sevenPow_sub_one_mod7 r

/-- The generated a = 5 factor `x+1` has residue `6` modulo 7. -/
theorem A75_plus_one_val_mod7 (r : ℕ) :
    (A75 r + 1).val % 7 = 6 := by
  rw [A75_plus_one_eq_natCast r]
  rw [natCast_val_mod7Step_mod7 r]
  exact five_pow_sevenPow_add_one_mod7 r

/-- The generated a = 5 non-target cyclotomic factor `Phi3(A75 r)` has residue
`3` modulo 7. -/
theorem Phi3_A75_val_mod7 (r : ℕ) :
    (Phi3 (A75 r)).val % 7 = 3 := by
  rw [Phi3_A75_eq_natCast r]
  rw [natCast_val_mod7Step_mod7 r]
  exact phi3_five_pow_sevenPow_mod7 r

/-!
Step 6D.  Unit-free generated branch correctness.
-/

/-- Generated a = 4 branch: the cubic test is equivalent to the quadratic
`Phi3` test, with the unit condition discharged automatically. -/
theorem a4_generated_quadratic_test_correct_auto (r : ℕ) :
    CubicNaiveTest r (A74 r) ↔ Phi3Test r (A74 r) := by
  exact a4_generated_quadratic_test_correct_of_val r
    (A74_minus_one_val_mod7 r)

/-- Generated a = 5 branch: the sixth-power test is equivalent to the quadratic
`Phi6` test, with all non-target unit conditions discharged automatically. -/
theorem a5_generated_quadratic_test_correct_auto (r : ℕ) :
    SixthNaiveTest r (A75 r) ↔ Phi6Test r (A75 r) := by
  exact a5_generated_quadratic_test_correct_of_val r
    (A75_minus_one_val_mod7 r)
    (A75_plus_one_val_mod7 r)
    (Phi3_A75_val_mod7 r)

end QuadraticCyclotomicLift2
