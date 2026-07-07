import ABD.Memo.QuadraticCyclotomicLift2_GeneratedZero

/-
QuadraticCyclotomicLift2_ExtraLiftPredicate.lean

Continuation of the p = 7 quadratic-cyclotomic route.

The previous files proved the guaranteed level:

  A74 r = 4^(7^r) passes the cubic test in ZMod (7^(r+1)),
  A75 r = 5^(7^r) passes the sixth-power test in ZMod (7^(r+1)),

and both tests reduce to the quadratic cyclotomic tests Phi_3 / Phi_6.

This file does not prove any concrete exceptional r.  It only introduces the
common language for asking whether the generated representative survives extra
7-adic digits:

  extra = 0  means the already-guaranteed modulus 7^(r+1),
  extra = 1  means one more digit, i.e. modulus 7^(r+2),
  extra = 2  means two more digits, i.e. modulus 7^(r+3),
  and so on.

The key point recorded here is that, at every extra level, the expensive naive
power test is still equivalent to the small quadratic cyclotomic test, once the
same non-target unit facts are available.
-/

namespace QuadraticCyclotomicLift2

/-!
Step 8A.  One uniform modulus for extra-lift questions.

The index `r` is the same index used by the previous files: the guaranteed
modulus is `7^(r+1)`.  The parameter `extra` counts how many additional 7-adic
digits we ask for beyond that guaranteed level.
-/

/-- The modulus used for checking `extra` additional 7-adic digits. -/
abbrev Mod7Extra (r extra : ℕ) := ZMod (7 ^ (r + 1 + extra))

/-- p = 7, a = 4 generated representative in the extra-check modulus. -/
def A74Extra (r extra : ℕ) : Mod7Extra r extra :=
  (4 : Mod7Extra r extra) ^ (7 ^ r)

/-- p = 7, a = 5 generated representative in the extra-check modulus. -/
def A75Extra (r extra : ℕ) : Mod7Extra r extra :=
  (5 : Mod7Extra r extra) ^ (7 ^ r)

/-!
Step 8B.  Naive and quadratic tests at the extra modulus.
-/

/-- Naive cubic test at the extra modulus. -/
def CubicNaiveExtraTest (r extra : ℕ) (x : Mod7Extra r extra) : Prop :=
  x ^ 3 - 1 = 0

/-- Quadratic Phi_3 test at the extra modulus. -/
def Phi3ExtraTest (r extra : ℕ) (x : Mod7Extra r extra) : Prop :=
  Phi3 x = 0

/-- Naive sixth-power test at the extra modulus. -/
def SixthNaiveExtraTest (r extra : ℕ) (x : Mod7Extra r extra) : Prop :=
  x ^ 6 - 1 = 0

/-- Quadratic Phi_6 test at the extra modulus. -/
def Phi6ExtraTest (r extra : ℕ) (x : Mod7Extra r extra) : Prop :=
  Phi6 x = 0

/-!
Step 8C.  The same quadratic reduction works at every extra modulus.
-/

/-- At every extra modulus, the cubic test is equivalent to the Phi_3 test. -/
theorem phi3_extra_test_correct
    (r extra : ℕ)
    (x : Mod7Extra r extra)
    (hunit : IsUnit (x - 1)) :
    CubicNaiveExtraTest r extra x ↔ Phi3ExtraTest r extra x := by
  unfold CubicNaiveExtraTest Phi3ExtraTest
  exact phi3_zero_iff_cube_zero_of_unit x hunit

/-- At every extra modulus, the sixth-power test is equivalent to the Phi_6 test. -/
theorem phi6_extra_test_correct
    (r extra : ℕ)
    (x : Mod7Extra r extra)
    (h1 : IsUnit (x - 1))
    (h2 : IsUnit (x + 1))
    (h3 : IsUnit (Phi3 x)) :
    SixthNaiveExtraTest r extra x ↔ Phi6ExtraTest r extra x := by
  unfold SixthNaiveExtraTest Phi6ExtraTest
  exact phi6_zero_iff_six_zero_of_units x h1 h2 h3

/-!
Step 8D.  Branch-specific forms of the extra-lift reduction.
-/

/-- Generated a = 4 branch: extra cubic testing reduces to Phi_3. -/
theorem a4_extra_quadratic_test_correct
    (r extra : ℕ)
    (hunit : IsUnit (A74Extra r extra - 1)) :
    CubicNaiveExtraTest r extra (A74Extra r extra) ↔
      Phi3ExtraTest r extra (A74Extra r extra) := by
  exact phi3_extra_test_correct r extra (A74Extra r extra) hunit

/-- Generated a = 5 branch: extra sixth-power testing reduces to Phi_6. -/
theorem a5_extra_quadratic_test_correct
    (r extra : ℕ)
    (h1 : IsUnit (A75Extra r extra - 1))
    (h2 : IsUnit (A75Extra r extra + 1))
    (h3 : IsUnit (Phi3 (A75Extra r extra))) :
    SixthNaiveExtraTest r extra (A75Extra r extra) ↔
      Phi6ExtraTest r extra (A75Extra r extra) := by
  exact phi6_extra_test_correct r extra (A75Extra r extra) h1 h2 h3

/-!
Step 8E.  LTE-friendly normal forms at the extra modulus.

These lemmas keep the same computational compression available at any extra
level.  They do not prove divisibility at that level; they only rewrite the
large power expressions into the small bases `64` and `15625`.
-/

/-- At the extra modulus, `(A74Extra r extra)^3 = 64^(7^r)`. -/
theorem A74Extra_cube_eq_64_pow (r extra : ℕ) :
    (A74Extra r extra) ^ 3 =
      (64 : Mod7Extra r extra) ^ (7 ^ r) := by
  unfold A74Extra
  calc
    ((4 : Mod7Extra r extra) ^ (7 ^ r)) ^ 3 =
        (4 : Mod7Extra r extra) ^ ((7 ^ r) * 3) := by
      rw [pow_mul]
    _ = (4 : Mod7Extra r extra) ^ (3 * (7 ^ r)) := by
      rw [Nat.mul_comm]
    _ = ((4 : Mod7Extra r extra) ^ 3) ^ (7 ^ r) := by
      rw [pow_mul]
    _ = (64 : Mod7Extra r extra) ^ (7 ^ r) := by
      have h64 : (4 : Mod7Extra r extra) ^ 3 = (64 : Mod7Extra r extra) := by
        norm_num
      rw [h64]

/-- At the extra modulus, `(A75Extra r extra)^6 = 15625^(7^r)`. -/
theorem A75Extra_sixth_eq_15625_pow (r extra : ℕ) :
    (A75Extra r extra) ^ 6 =
      (15625 : Mod7Extra r extra) ^ (7 ^ r) := by
  unfold A75Extra
  calc
    ((5 : Mod7Extra r extra) ^ (7 ^ r)) ^ 6 =
        (5 : Mod7Extra r extra) ^ ((7 ^ r) * 6) := by
      rw [pow_mul]
    _ = (5 : Mod7Extra r extra) ^ (6 * (7 ^ r)) := by
      rw [Nat.mul_comm]
    _ = ((5 : Mod7Extra r extra) ^ 6) ^ (7 ^ r) := by
      rw [pow_mul]
    _ = (15625 : Mod7Extra r extra) ^ (7 ^ r) := by
      have h15625 :
          (5 : Mod7Extra r extra) ^ 6 = (15625 : Mod7Extra r extra) := by
        norm_num
      rw [h15625]

/-- Extra cubic test for a = 4, rewritten into the LTE-friendly normal form. -/
theorem A74Extra_cubic_test_lte_form (r extra : ℕ) :
    CubicNaiveExtraTest r extra (A74Extra r extra) ↔
      (64 : Mod7Extra r extra) ^ (7 ^ r) - 1 = 0 := by
  unfold CubicNaiveExtraTest
  rw [A74Extra_cube_eq_64_pow]

/-- Extra sixth-power test for a = 5, rewritten into the LTE-friendly normal form. -/
theorem A75Extra_sixth_test_lte_form (r extra : ℕ) :
    SixthNaiveExtraTest r extra (A75Extra r extra) ↔
      (15625 : Mod7Extra r extra) ^ (7 ^ r) - 1 = 0 := by
  unfold SixthNaiveExtraTest
  rw [A75Extra_sixth_eq_15625_pow]

/-!
Step 8F.  Predicates for the exceptional / extra-lift search.

`extra = 0` is the guaranteed level already proved in the previous file.
`extra = 1` is the first genuinely extra digit.
-/

/-- The a = 4 branch survives to the extra modulus, expressed by Phi_3. -/
def A74HasExtraLift (r extra : ℕ) : Prop :=
  Phi3ExtraTest r extra (A74Extra r extra)

/-- The a = 5 branch survives to the extra modulus, expressed by Phi_6. -/
def A75HasExtraLift (r extra : ℕ) : Prop :=
  Phi6ExtraTest r extra (A75Extra r extra)

/-- The a = 4 branch has at least one extra 7-adic digit beyond the guaranteed level. -/
def A74HasOneMoreDigit (r : ℕ) : Prop :=
  A74HasExtraLift r 1

/-- The a = 5 branch has at least one extra 7-adic digit beyond the guaranteed level. -/
def A75HasOneMoreDigit (r : ℕ) : Prop :=
  A75HasExtraLift r 1

/-- The a = 4 branch has at least two extra 7-adic digits beyond the guaranteed level. -/
def A74HasTwoMoreDigits (r : ℕ) : Prop :=
  A74HasExtraLift r 2

/-- The a = 5 branch has at least two extra 7-adic digits beyond the guaranteed level. -/
def A75HasTwoMoreDigits (r : ℕ) : Prop :=
  A75HasExtraLift r 2

end QuadraticCyclotomicLift2
