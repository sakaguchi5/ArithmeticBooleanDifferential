import ABD.Memo.QuadraticCyclotomicLift2_Generation
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.NormNum

/-
QuadraticCyclotomicLift2_UnitAuto.lean

Continuation of the p = 7 quadratic-cyclotomic route.

Purpose:
  The first file proved the quadratic reduction under explicit unit hypotheses.
  The generation file recorded the generated representatives and mod-7 seed
  residue checks.

This file adds the reusable unit-automation bridge:

  if x : ZMod (7^(r+1)) has representative value not divisible by 7,
  then x is a unit.

For the p = 7 branches this means that the explicit unit hypotheses can be
replaced by small residue checks modulo 7.

This file intentionally does not yet prove the generated residue facts such as
  (A74 r - 1).val % 7 = 3.
It packages the exact bridge that consumes those residue facts.
-/

namespace QuadraticCyclotomicLift2

/-!
Step 5A.  Generic unit automation in `ZMod (7^(r+1))`.

The key local-ring fact is:
  in ZMod (7^(r+1)), an element is a unit as soon as its representative is not
  divisible by 7.

We phrase this using `.val % 7 ≠ 0`, because that is exactly what the small
residue computations provide.
-/

/-- `7^(r+1)` is nonzero, as a typeclass instance for using `ZMod.val`. -/
instance neZero_mod7Step_modulus (r : ℕ) : NeZero (7 ^ (r + 1)) :=
  ⟨by exact pow_ne_zero (r + 1) (by norm_num : (7 : ℕ) ≠ 0)⟩

/--
If the representative of `x : ZMod (7^(r+1))` is nonzero modulo 7, then `x` is a
unit.
-/
theorem unit_of_val_mod7_ne_zero
    (r : ℕ)
    (x : Mod7Step r)
    (h : x.val % 7 ≠ 0) :
    IsUnit x := by
  haveI : NeZero (7 ^ (r + 1)) := neZero_mod7Step_modulus r
  have hx : ((x.val : ℕ) : Mod7Step r) = x := by
    exact ZMod.natCast_zmod_val x
  rw [← hx]
  rw [ZMod.isUnit_iff_coprime]
  have hnotdvd : ¬ 7 ∣ x.val := by
    simpa [Nat.dvd_iff_mod_eq_zero] using h
  have hprime7 : Nat.Prime 7 := by
    decide
  have hcop7 : x.val.Coprime 7 := by
    exact ((Nat.Prime.coprime_iff_not_dvd hprime7).2 hnotdvd).symm
  exact hcop7.pow_right (r + 1)

/-- Convenience wrapper when the residue is known to be `3`. -/
theorem unit_of_val_mod7_eq_three
    (r : ℕ)
    (x : Mod7Step r)
    (h : x.val % 7 = 3) :
    IsUnit x := by
  exact unit_of_val_mod7_ne_zero r x (by simp [h])

/-- Convenience wrapper when the residue is known to be `4`. -/
theorem unit_of_val_mod7_eq_four
    (r : ℕ)
    (x : Mod7Step r)
    (h : x.val % 7 = 4) :
    IsUnit x := by
  exact unit_of_val_mod7_ne_zero r x (by simp [h])

/-- Convenience wrapper when the residue is known to be `6`. -/
theorem unit_of_val_mod7_eq_six
    (r : ℕ)
    (x : Mod7Step r)
    (h : x.val % 7 = 6) :
    IsUnit x := by
  exact unit_of_val_mod7_ne_zero r x (by simp [h])

/-!
Step 5B.  Unit hypotheses for the p = 7 generated branches, expressed as
small residue checks.

These lemmas replace raw `IsUnit` assumptions by residue equalities modulo 7.
The remaining target for a later file is to prove the residue equalities from
`A74 r = 4^(7^r)` and `A75 r = 5^(7^r)`.
-/

/-- For the a = 4 branch, `A74 r - 1` is a unit once its mod-7 residue is `3`. -/
theorem a4_nonPhi3_factor_unit_auto_of_val
    (r : ℕ)
    (h : (A74 r - 1).val % 7 = 3) :
    IsUnit (A74 r - 1) := by
  exact unit_of_val_mod7_eq_three r (A74 r - 1) h

/-- For the a = 5 branch, `A75 r - 1` is a unit once its mod-7 residue is `4`. -/
theorem a5_factor_x_minus_one_unit_auto_of_val
    (r : ℕ)
    (h : (A75 r - 1).val % 7 = 4) :
    IsUnit (A75 r - 1) := by
  exact unit_of_val_mod7_eq_four r (A75 r - 1) h

/-- For the a = 5 branch, `A75 r + 1` is a unit once its mod-7 residue is `6`. -/
theorem a5_factor_x_plus_one_unit_auto_of_val
    (r : ℕ)
    (h : (A75 r + 1).val % 7 = 6) :
    IsUnit (A75 r + 1) := by
  exact unit_of_val_mod7_eq_six r (A75 r + 1) h

/-- For the a = 5 branch, `Phi3 (A75 r)` is a unit once its mod-7 residue is `3`. -/
theorem a5_factor_phi3_unit_auto_of_val
    (r : ℕ)
    (h : (Phi3 (A75 r)).val % 7 = 3) :
    IsUnit (Phi3 (A75 r)) := by
  exact unit_of_val_mod7_eq_three r (Phi3 (A75 r)) h

/-!
Step 5C.  Final generated-branch correctness statements with unit automation
inserted.

Compared with the first file, these theorems no longer ask for `IsUnit` facts
directly.  They ask only for the tiny residue facts modulo 7.
-/

/--
Generated a = 4 branch: the cubic test equals the quadratic `Phi3` test, once
`A74 r - 1` is known to have residue `3` modulo 7.
-/
theorem a4_generated_quadratic_test_correct_of_val
    (r : ℕ)
    (h : (A74 r - 1).val % 7 = 3) :
    CubicNaiveTest r (A74 r) ↔ Phi3Test r (A74 r) := by
  exact a4_branch_quadratic_test_correct r
    (a4_nonPhi3_factor_unit_auto_of_val r h)

/--
Generated a = 5 branch: the sixth-power test equals the quadratic `Phi6` test,
once the non-target factors have the expected nonzero residues modulo 7.
-/
theorem a5_generated_quadratic_test_correct_of_val
    (r : ℕ)
    (h1 : (A75 r - 1).val % 7 = 4)
    (h2 : (A75 r + 1).val % 7 = 6)
    (h3 : (Phi3 (A75 r)).val % 7 = 3) :
    SixthNaiveTest r (A75 r) ↔ Phi6Test r (A75 r) := by
  exact a5_branch_quadratic_test_correct r
    (a5_factor_x_minus_one_unit_auto_of_val r h1)
    (a5_factor_x_plus_one_unit_auto_of_val r h2)
    (a5_factor_phi3_unit_auto_of_val r h3)

end QuadraticCyclotomicLift2
