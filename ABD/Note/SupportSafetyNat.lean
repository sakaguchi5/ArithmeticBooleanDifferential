import ABD.Note.SupportSafety
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Support safety: connection to natural-number radicals

This file remains independent from the rest of ABD.  It connects the abstract
log-weight accounting in `ABD.Note.SupportSafety` to a concrete natural-number
radical definition.

The proofs here deliberately keep the arithmetic side light.  The core safety
lemmas still live at the logarithmic-accounting level; the natural-number
objects are wrappers around that accounting.
-/

namespace ABD
namespace Note


/-- The radical of a natural number, as the product of the prime support. -/
def natRad (n : ℕ) : ℕ :=
  n.factorization.support.prod id

/-- Natural-number logarithmic scale: `log₂ n`. -/
noncomputable def natLogScale (n : ℕ) : ℝ :=
  log2 (n : ℝ)

/-- Natural-number logarithmic radical: `log₂ rad(n)`. -/
noncomputable def natLogRad (n : ℕ) : ℝ :=
  log2 (natRad n : ℝ)

/-- Natural-number danger score. -/
noncomputable def natDanger (α : ℝ) (n : ℕ) : ℝ :=
  danger α (natLogScale n) (natLogRad n)

/-- Unfolding form of the natural-number danger score. -/
theorem natDanger_eq (α : ℝ) (n : ℕ) :
    natDanger α n = log2 (n : ℝ) - α * log2 (natRad n : ℝ) := by
  rfl

/--
Natural-number qualitative safety theorem.

If two natural numbers are compared at the same logarithmic scale and the second
has larger logarithmic radical, then the second is safer.
-/
theorem natDanger_lt_of_same_scale_of_logRad_lt
    {α : ℝ} {a b : ℕ}
    (hα : 0 < α)
    (hscale : natLogScale a = natLogScale b)
    (hrad : natLogRad a < natLogRad b) :
    natDanger α b < natDanger α a := by
  unfold natDanger
  rw [← hscale]
  exact larger_logRad_is_safer hα hrad

/--
Natural-number support-addition safety theorem.

This is the direct bridge from the natural radical wrapper to the abstract
support-log theorem: if the added support has positive total logarithmic weight,
then the new natural-number danger score is lower, provided the natural-number
scale is held fixed and the new radical log is the old radical log plus that
support weight.
-/
theorem natDanger_lt_of_added_positive_support
    {ι : Type u} {α : ℝ} {a b : ℕ} {S : Finset ι} {w : ι → ℝ}
    (hα : 0 < α)
    (hscale : natLogScale a = natLogScale b)
    (hrad : natLogRad b = natLogRad a + supportLog S w)
    (hS : 0 < supportLog S w) :
    natDanger α b < natDanger α a := by
  unfold natDanger
  rw [← hscale, hrad]
  exact adding_positive_support_is_safer hα hS

/--
Monotonicity of base-2 logarithm on the positive reals.
-/
theorem log2_le_log2_of_pos_of_le {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) :
    log2 x ≤ log2 y := by
  unfold log2
  have hlog : Real.log x ≤ Real.log y :=
    Real.log_le_log hx hxy
  have hden : 0 ≤ Real.log 2 := by
    exact le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  exact div_le_div_of_nonneg_right hlog hden

/--
If a natural support value is at least `3`, then its base-2 log-weight is at
least `log₂ 3`.

For an odd prime support `q`, the intended use is to first provide the elementary
arithmetic fact `3 ≤ q`.
-/
theorem log2_nat_ge_log2_three_of_three_le {q : ℕ}
    (hq : 3 ≤ q) :
    log2 3 ≤ log2 (q : ℝ) := by
  exact log2_le_log2_of_pos_of_le
    (by norm_num : (0 : ℝ) < 3)
    (by exact_mod_cast hq)

/--
Pointwise natural support version of the rough `log₂ 3` lower bound.
-/
theorem support_drop_lower_bound_by_nat_supports_log2_three
    {ι : Type u} {α : ℝ} {S : Finset ι} {q : ι → ℕ}
    (hα : 0 ≤ α)
    (hq : ∀ i, i ∈ S → 3 ≤ q i) :
    α * ((S.card : ℝ) * log2 3)
      ≤ supportDrop α S (fun i => log2 (q i : ℝ)) := by
  exact support_drop_lower_bound_by_card_log2_three
    (S := S)
    (w := fun i => log2 (q i : ℝ))
    hα
    (fun i hi => log2_nat_ge_log2_three_of_three_le (hq i hi))

/--
Danger-score version of the natural support `log₂ 3` bound.
-/
theorem danger_after_adding_nat_supports_le_log2_three
    {ι : Type u} {α scale logRad : ℝ} {S : Finset ι} {q : ι → ℕ}
    (hα : 0 ≤ α)
    (hq : ∀ i, i ∈ S → 3 ≤ q i) :
    danger α scale (logRad + supportLog S (fun i => log2 (q i : ℝ)))
      ≤ danger α scale logRad - α * ((S.card : ℝ) * log2 3) := by
  exact danger_after_adding_support_le_by_card_log2_three
    (S := S)
    (w := fun i => log2 (q i : ℝ))
    hα
    (fun i hi => log2_nat_ge_log2_three_of_three_le (hq i hi))


end Note
end ABD
