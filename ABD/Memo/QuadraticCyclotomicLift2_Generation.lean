import ABD.Memo.QuadraticCyclotomicLift2
import Mathlib.Tactic.NormNum

/-
QuadraticCyclotomicLift2_Generation.lean

Continuation of `ABD/Memo/QuadraticCyclotomicLift2.lean`.

The previous file proved the quadratic-cyclotomic reduction:
  * for the a = 4 branch, the cubic test reduces to Phi_3;
  * for the a = 5 branch, the sixth-power test reduces to Phi_6,
    assuming the other cyclotomic factors are units.

This file records the generated representatives used by the p = 7 route and
keeps the next bridge target explicit:
  * A_4(r) = 4^(7^r), so A_4(r)^3 is 64^(7^r);
  * A_5(r) = 5^(7^r), so A_5(r)^6 is 15625^(7^r);
  * the mod-7 residue checks identifying the non-target factors as nonzero.

The point is to justify, in a small Lean-friendly form, why the high-power
checks are converted to small cyclotomic checks before doing any large integer
calculation.
-/

namespace QuadraticCyclotomicLift2

/-!
Step 4A.
Natural-number generated representatives for the p = 7, quadratic branches.
These are the integer versions of the modular representatives `A74` and `A75`
from the previous file.
-/

/-- Natural-number generated representative for p = 7, a = 4. -/
def A74Nat (r : ℕ) : ℕ :=
  4 ^ (7 ^ r)

/-- Natural-number generated representative for p = 7, a = 5. -/
def A75Nat (r : ℕ) : ℕ :=
  5 ^ (7 ^ r)

/-- The a = 4 cubic expression is the LTE-friendly expression 64^(7^r). -/
theorem A74Nat_cube_eq_64_pow (r : ℕ) :
    (A74Nat r) ^ 3 = 64 ^ (7 ^ r) := by
  unfold A74Nat
  calc
    (4 ^ (7 ^ r)) ^ 3 = 4 ^ ((7 ^ r) * 3) := by
      rw [pow_mul]
    _ = 4 ^ (3 * (7 ^ r)) := by
      rw [Nat.mul_comm]
    _ = (4 ^ 3) ^ (7 ^ r) := by
      rw [pow_mul]
    _ = 64 ^ (7 ^ r) := by
      norm_num

/-- Subtracting 1 preserves the a = 4 LTE-friendly normal form. -/
theorem A74Nat_cube_sub_one_eq_64_pow_sub_one (r : ℕ) :
    (A74Nat r) ^ 3 - 1 = 64 ^ (7 ^ r) - 1 := by
  rw [A74Nat_cube_eq_64_pow]

/-- The a = 5 sixth-power expression is the LTE-friendly expression 15625^(7^r). -/
theorem A75Nat_sixth_eq_15625_pow (r : ℕ) :
    (A75Nat r) ^ 6 = 15625 ^ (7 ^ r) := by
  unfold A75Nat
  calc
    (5 ^ (7 ^ r)) ^ 6 = 5 ^ ((7 ^ r) * 6) := by
      rw [pow_mul]
    _ = 5 ^ (6 * (7 ^ r)) := by
      rw [Nat.mul_comm]
    _ = (5 ^ 6) ^ (7 ^ r) := by
      rw [pow_mul]
    _ = 15625 ^ (7 ^ r) := by
      norm_num

/-- Subtracting 1 preserves the a = 5 LTE-friendly normal form. -/
theorem A75Nat_sixth_sub_one_eq_15625_pow_sub_one (r : ℕ) :
    (A75Nat r) ^ 6 - 1 = 15625 ^ (7 ^ r) - 1 := by
  rw [A75Nat_sixth_eq_15625_pow]

/-!
Step 4B.
The same normal forms inside the one-step-higher modulus `ZMod (7^(r+1))`.
These lemmas let the previous quadratic tests consume the generated `A74` and
`A75` without expanding the large powers directly.
-/

/-- In `ZMod (7^(r+1))`, the generated a = 4 branch satisfies A^3 = 64^(7^r). -/
theorem A74_cube_eq_64_pow (r : ℕ) :
    (A74 r) ^ 3 = (64 : Mod7Step r) ^ (7 ^ r) := by
  unfold A74
  calc
    ((4 : Mod7Step r) ^ (7 ^ r)) ^ 3 =
        (4 : Mod7Step r) ^ ((7 ^ r) * 3) := by
      rw [pow_mul]
    _ = (4 : Mod7Step r) ^ (3 * (7 ^ r)) := by
      rw [Nat.mul_comm]
    _ = ((4 : Mod7Step r) ^ 3) ^ (7 ^ r) := by
      rw [pow_mul]
    _ = (64 : Mod7Step r) ^ (7 ^ r) := by
      have h64 : (4 : Mod7Step r) ^ 3 = (64 : Mod7Step r) := by
        norm_num
      rw [h64]

/-- In `ZMod (7^(r+1))`, the generated a = 5 branch satisfies A^6 = 15625^(7^r). -/
theorem A75_sixth_eq_15625_pow (r : ℕ) :
    (A75 r) ^ 6 = (15625 : Mod7Step r) ^ (7 ^ r) := by
  unfold A75
  calc
    ((5 : Mod7Step r) ^ (7 ^ r)) ^ 6 =
        (5 : Mod7Step r) ^ ((7 ^ r) * 6) := by
      rw [pow_mul]
    _ = (5 : Mod7Step r) ^ (6 * (7 ^ r)) := by
      rw [Nat.mul_comm]
    _ = ((5 : Mod7Step r) ^ 6) ^ (7 ^ r) := by
      rw [pow_mul]
    _ = (15625 : Mod7Step r) ^ (7 ^ r) := by
      have h15625 : (5 : Mod7Step r) ^ 6 = (15625 : Mod7Step r) := by
        norm_num
      rw [h15625]

/-- The naive cubic test for generated a = 4 can be rewritten into LTE form. -/
theorem A74_cubic_test_lte_form (r : ℕ) :
    CubicNaiveTest r (A74 r) ↔
      (64 : Mod7Step r) ^ (7 ^ r) - 1 = 0 := by
  unfold CubicNaiveTest
  rw [A74_cube_eq_64_pow]

/-- The naive sixth-power test for generated a = 5 can be rewritten into LTE form. -/
theorem A75_sixth_test_lte_form (r : ℕ) :
    SixthNaiveTest r (A75 r) ↔
      (15625 : Mod7Step r) ^ (7 ^ r) - 1 = 0 := by
  unfold SixthNaiveTest
  rw [A75_sixth_eq_15625_pow]

/-!
Step 4C.
Mod-7 residue checks for the non-target cyclotomic factors.

These are the small residue facts behind the unit hypotheses in the previous
file.  The next bridge is to lift these nonzero mod-7 residues into automatic
unit facts in `ZMod (7^(r+1))`.
-/

/-- Seed residue for the a = 4 branch: Phi_3(4) vanishes mod 7. -/
theorem seed_a4_phi3_mod7 :
    Phi3 (4 : ZMod 7) = 0 := by
  norm_num [Phi3]
  decide

/-- Seed residue for the a = 4 non-target factor: 4 - 1 = 3 mod 7. -/
theorem seed_a4_nonPhi3_factor_mod7 :
    (4 : ZMod 7) - 1 = 3 := by
  norm_num

/-- Seed residue for the a = 5 branch: Phi_6(5) vanishes mod 7. -/
theorem seed_a5_phi6_mod7 :
    Phi6 (5 : ZMod 7) = 0 := by
  norm_num [Phi6]
  decide

/-- Non-target factor for a = 5: 5 - 1 = 4 mod 7. -/
theorem seed_a5_x_minus_one_mod7 :
    (5 : ZMod 7) - 1 = 4 := by
  norm_num

/-- Non-target factor for a = 5: 5 + 1 = 6 mod 7. -/
theorem seed_a5_x_plus_one_mod7 :
    (5 : ZMod 7) + 1 = 6 := by
  norm_num

/-- Non-target cyclotomic factor for a = 5: Phi_3(5) = 3 mod 7. -/
theorem seed_a5_phi3_mod7 :
    Phi3 (5 : ZMod 7) = 3 := by
  norm_num [Phi3]
  decide

end QuadraticCyclotomicLift2
