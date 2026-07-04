import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
/-
QuadraticCyclotomicLift2.lean

Goal of this file:
  Keep the 2-dimensional / quadratic cyclotomic version of the algorithm.

Main idea:
  For p = 7, the non-trivial non-(-1) branches are controlled by

    Phi_3(x) = x^2 + x + 1
    Phi_6(x) = x^2 - x + 1

  Therefore the expensive checks

    x^3 - 1 = 0  mod 7^(r+1)
    x^6 - 1 = 0  mod 7^(r+1)

  can be replaced by the smaller quadratic checks

    Phi_3(x) = 0 mod 7^(r+1)
    Phi_6(x) = 0 mod 7^(r+1)

  once the other cyclotomic factors are known to be units.

This is deliberately written as a small standalone file with only the imports
needed for ring normalization and ZMod.
-/

namespace QuadraticCyclotomicLift2

/-!
Step 1.
Define the two quadratic cyclotomic polynomials that occur for p = 7:
  Phi_3(x) = x^2 + x + 1
  Phi_6(x) = x^2 - x + 1
and prove the elementary factorization identities.
-/


variable {R : Type*} [CommRing R]

/-- The quadratic cyclotomic polynomial Phi_3(x) = x^2 + x + 1. -/
def Phi3 (x : R) : R :=
  x ^ 2 + x + 1

/-- The quadratic cyclotomic polynomial Phi_6(x) = x^2 - x + 1. -/
def Phi6 (x : R) : R :=
  x ^ 2 - x + 1

/-- x^3 - 1 = (x - 1) Phi_3(x). -/
theorem phi3_factor (x : R) :
    (x - 1) * Phi3 x = x ^ 3 - 1 := by
  unfold Phi3
  ring

/-- x^3 + 1 = (x + 1) Phi_6(x). -/
theorem phi6_factor_cubic_plus (x : R) :
    (x + 1) * Phi6 x = x ^ 3 + 1 := by
  unfold Phi6
  ring

/-- x^6 - 1 = (x - 1)(x + 1)Phi_3(x)Phi_6(x). -/
theorem phi6_factor_six (x : R) :
    ((x - 1) * (x + 1) * Phi3 x) * Phi6 x = x ^ 6 - 1 := by
  unfold Phi3 Phi6
  ring

/-!
Step 2.
A unit factor can be removed from a zero test.
This is the algebraic core behind the algorithmic reduction.
-/

lemma eq_zero_of_isUnit_mul_eq_zero
    {a b : R}
    (ha : IsUnit a)
    (h : a * b = 0) :
    b = 0 := by
  rcases ha with ⟨u, rfl⟩
  have h' := congrArg (fun y : R => (↑u⁻¹ : R) * y) h
  simpa [mul_assoc] using h'

/--
If x - 1 is a unit, then checking x^3 - 1 = 0 is equivalent to
checking Phi_3(x) = 0.
-/
theorem phi3_zero_iff_cube_zero_of_unit
    (x : R)
    (hunit : IsUnit (x - 1)) :
    x ^ 3 - 1 = 0 ↔ Phi3 x = 0 := by
  constructor
  · intro h
    have hmul : (x - 1) * Phi3 x = 0 := by
      rw [phi3_factor]
      exact h
    exact eq_zero_of_isUnit_mul_eq_zero hunit hmul
  · intro h
    rw [← phi3_factor]
    simp [h]

/--
If the other cyclotomic factors are units, then checking x^6 - 1 = 0 is
equivalent to checking Phi_6(x) = 0.
-/
theorem phi6_zero_iff_six_zero_of_units
    (x : R)
    (h1 : IsUnit (x - 1))
    (h2 : IsUnit (x + 1))
    (h3 : IsUnit (Phi3 x)) :
    x ^ 6 - 1 = 0 ↔ Phi6 x = 0 := by
  constructor
  · intro h
    have hcoef : IsUnit ((x - 1) * (x + 1) * Phi3 x) := by
      exact (h1.mul h2).mul h3
    have hmul : ((x - 1) * (x + 1) * Phi3 x) * Phi6 x = 0 := by
      rw [phi6_factor_six]
      exact h
    exact eq_zero_of_isUnit_mul_eq_zero hcoef hmul
  · intro h
    rw [← phi6_factor_six]
    simp [h]

/-!
Step 3.
Specialize the zero tests to ZMod (7^(r+1)).

Interpretation:
  In ZMod (7^(r+1)), equality to 0 means divisibility by 7^(r+1).
  Therefore these theorems justify checking only the quadratic Phi_3 / Phi_6
  instead of the large powers x^3 - 1 or x^6 - 1.

The unit hypotheses are kept explicit here.  For the intended p = 7 branches,
they are supplied from the residue class:
  * a = 4 branch: x is congruent to 4 mod 7, so x - 1 is a unit.
  * a = 5 branch: x is congruent to 5 mod 7, so x - 1, x + 1,
    and Phi_3(x) are units.
-/

abbrev Mod7Step (r : ℕ) := ZMod (7 ^ (r + 1))

/-- Naive cubic test in modulus 7^(r+1). -/
def CubicNaiveTest (r : ℕ) (x : Mod7Step r) : Prop :=
  x ^ 3 - 1 = 0

/-- Quadratic Phi_3 test in modulus 7^(r+1). -/
def Phi3Test (r : ℕ) (x : Mod7Step r) : Prop :=
  Phi3 x = 0

/-- Naive sixth-power test in modulus 7^(r+1). -/
def SixthNaiveTest (r : ℕ) (x : Mod7Step r) : Prop :=
  x ^ 6 - 1 = 0

/-- Quadratic Phi_6 test in modulus 7^(r+1). -/
def Phi6Test (r : ℕ) (x : Mod7Step r) : Prop :=
  Phi6 x = 0

/-- Correctness of the Phi_3 quadratic test in ZMod (7^(r+1)). -/
theorem phi3_test_correct_mod7
    (r : ℕ)
    (x : Mod7Step r)
    (hunit : IsUnit (x - 1)) :
    CubicNaiveTest r x ↔ Phi3Test r x := by
  unfold CubicNaiveTest Phi3Test
  exact phi3_zero_iff_cube_zero_of_unit x hunit

/-- Correctness of the Phi_6 quadratic test in ZMod (7^(r+1)). -/
theorem phi6_test_correct_mod7
    (r : ℕ)
    (x : Mod7Step r)
    (h1 : IsUnit (x - 1))
    (h2 : IsUnit (x + 1))
    (h3 : IsUnit (Phi3 x)) :
    SixthNaiveTest r x ↔ Phi6Test r x := by
  unfold SixthNaiveTest Phi6Test
  exact phi6_zero_iff_six_zero_of_units x h1 h2 h3

/-!
Step 4.
Connect the tests to the p = 7, a = 4 and a = 5 branches.

These definitions are the one-step-higher modular representatives used by the
algorithmic check.  For checking whether the current representative survives
one more 7-adic digit, the computation is performed in ZMod (7^(r+1)).

The theorems below say: once a concrete generated representative is available
in this modulus and the expected unit facts are known, the expensive power test
is equivalent to the quadratic cyclotomic test.
-/

/-- p = 7, a = 4 candidate in modulus 7^(r+1). -/
def A74 (r : ℕ) : Mod7Step r :=
  (4 : Mod7Step r) ^ (7 ^ r)

/-- p = 7, a = 5 candidate in modulus 7^(r+1). -/
def A75 (r : ℕ) : Mod7Step r :=
  (5 : Mod7Step r) ^ (7 ^ r)

/--
For the a = 4 branch, the naive cubic test is equivalent to the Phi_3 test.
The hypothesis says the non-Phi_3 factor x - 1 is a unit.
-/
theorem a4_branch_quadratic_test_correct
    (r : ℕ)
    (hunit : IsUnit (A74 r - 1)) :
    CubicNaiveTest r (A74 r) ↔ Phi3Test r (A74 r) := by
  exact phi3_test_correct_mod7 r (A74 r) hunit

/--
For the a = 5 branch, the naive sixth-power test is equivalent to the Phi_6 test.
The hypotheses say all non-Phi_6 cyclotomic factors are units.
-/
theorem a5_branch_quadratic_test_correct
    (r : ℕ)
    (h1 : IsUnit (A75 r - 1))
    (h2 : IsUnit (A75 r + 1))
    (h3 : IsUnit (Phi3 (A75 r))) :
    SixthNaiveTest r (A75 r) ↔ Phi6Test r (A75 r) := by
  exact phi6_test_correct_mod7 r (A75 r) h1 h2 h3

end QuadraticCyclotomicLift2
