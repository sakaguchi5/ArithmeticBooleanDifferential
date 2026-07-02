import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Support safety notes

This file is intentionally independent from the rest of ABD.

It formalizes the elementary log-accounting principle discussed in the notes:
for a fixed scale, increasing radical/support makes the danger score smaller.

The intended arithmetic reading is:

* `scale = log₂(a)`.
* `logRad = log₂(rad(a))`.
* `w i = log₂(q_i)` for a newly added prime support `q_i`.
* `S : Finset ι` is the set of newly added supports, so supports are counted
  without repetition.

The file avoids using the existing ABD radical definitions.  It only proves the
coarse support-scale accounting lemma at the level of real logarithmic weights.
-/

namespace ABD
namespace Note

noncomputable section

open scoped BigOperators

/-- Base-2 logarithm, used only as notation for comments/corollaries. -/
def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/--
Single-integer danger score at fixed logarithmic scale.

Arithmetic reading:
`danger α scale logRad = log₂(a) - α log₂(rad(a))`.
-/
def danger (α scale logRad : ℝ) : ℝ :=
  scale - α * logRad

/-- Total logarithmic weight of a finite support set. -/
def supportLog {ι : Type u} (S : Finset ι) (w : ι → ℝ) : ℝ :=
  ∑ i in S, w i

/--
The danger drop caused by adding a support set with logarithmic weights `w`.
-/
def supportDrop {ι : Type u} (α : ℝ) (S : Finset ι) (w : ι → ℝ) : ℝ :=
  α * supportLog S w

/--
Qualitative safety theorem.

At fixed scale, if the logarithmic radical increases, then the danger strictly
decreases.  This is the formal version of:

"new support is always safer".
-/
theorem larger_logRad_is_safer
    {α scale oldRad newRad : ℝ}
    (hα : 0 < α) (hRad : oldRad < newRad) :
    danger α scale newRad < danger α scale oldRad := by
  have hmul : α * oldRad < α * newRad :=
    mul_lt_mul_of_pos_left hRad hα
  have hneg : -(α * newRad) < -(α * oldRad) :=
    neg_lt_neg hmul
  have hadd : scale + -(α * newRad) < scale + -(α * oldRad) :=
    add_lt_add_left hneg scale
  simpa [danger, sub_eq_add_neg] using hadd

/--
Support-addition form of the qualitative theorem.

If the newly added support has positive total log-weight, then adding it to the
log-radical strictly decreases danger.
-/
theorem adding_positive_support_is_safer
    {ι : Type u} {α scale logRad : ℝ} {S : Finset ι} {w : ι → ℝ}
    (hα : 0 < α) (hS : 0 < supportLog S w) :
    danger α scale (logRad + supportLog S w) < danger α scale logRad := by
  exact larger_logRad_is_safer hα (lt_add_of_pos_right logRad hS)

/--
Exact accounting identity.

Adding a new support set changes `logRad` by `supportLog S w`, hence the danger
score drops exactly by `α * supportLog S w`.
-/
theorem danger_after_adding_support_eq
    {ι : Type u} (α scale logRad : ℝ) (S : Finset ι) (w : ι → ℝ) :
    danger α scale (logRad + supportLog S w)
      = danger α scale logRad - supportDrop α S w := by
  simp [danger, supportDrop, supportLog, mul_add, sub_eq_add_neg, add_assoc]

/--
Coarse quantitative support-safety theorem.

If every newly added support has logarithmic weight at least `c`, then the total
support-safety drop is at least `α * |S| * c`.

For odd prime supports one may instantiate `c = log2 3`, giving the rough bound
`α * r * log2 3` where `r = S.card`.
-/
theorem support_drop_lower_bound_by_card
    {ι : Type u} {α c : ℝ} {S : Finset ι} {w : ι → ℝ}
    (hα : 0 ≤ α) (hw : ∀ i ∈ S, c ≤ w i) :
    α * ((S.card : ℝ) * c) ≤ supportDrop α S w := by
  have hsum : (S.card : ℝ) * c ≤ supportLog S w := by
    calc
      (S.card : ℝ) * c = ∑ _ in S, c := by
        simp
      _ ≤ ∑ i in S, w i := by
        exact Finset.sum_le_sum hw
      _ = supportLog S w := by
        rfl
  simpa [supportDrop] using mul_le_mul_of_nonneg_left hsum hα

/--
Danger-score version of the coarse quantitative theorem.

After adding support whose every log-weight is at least `c`, the new danger is at
most the old danger minus `α * |S| * c`.
-/
theorem danger_after_adding_support_le_by_card
    {ι : Type u} {α c scale logRad : ℝ} {S : Finset ι} {w : ι → ℝ}
    (hα : 0 ≤ α) (hw : ∀ i ∈ S, c ≤ w i) :
    danger α scale (logRad + supportLog S w)
      ≤ danger α scale logRad - α * ((S.card : ℝ) * c) := by
  have hdrop : α * ((S.card : ℝ) * c) ≤ supportDrop α S w :=
    support_drop_lower_bound_by_card (S := S) (w := w) hα hw
  have hsub :
      danger α scale logRad - supportDrop α S w
        ≤ danger α scale logRad - α * ((S.card : ℝ) * c) :=
    sub_le_sub_left hdrop (danger α scale logRad)
  calc
    danger α scale (logRad + supportLog S w)
        = danger α scale logRad - supportDrop α S w :=
          danger_after_adding_support_eq α scale logRad S w
    _ ≤ danger α scale logRad - α * ((S.card : ℝ) * c) := hsub

/--
The common rough odd-support bound.

If every support weight is at least `log₂ 3`, then the total support-safety drop
is at least `α * |S| * log₂ 3`.
-/
theorem support_drop_lower_bound_by_card_log2_three
    {ι : Type u} {α : ℝ} {S : Finset ι} {w : ι → ℝ}
    (hα : 0 ≤ α) (hw : ∀ i ∈ S, log2 3 ≤ w i) :
    α * ((S.card : ℝ) * log2 3) ≤ supportDrop α S w :=
  support_drop_lower_bound_by_card (S := S) (w := w) hα hw

/--
Danger-score version of the rough odd-support bound.
-/
theorem danger_after_adding_support_le_by_card_log2_three
    {ι : Type u} {α scale logRad : ℝ} {S : Finset ι} {w : ι → ℝ}
    (hα : 0 ≤ α) (hw : ∀ i ∈ S, log2 3 ≤ w i) :
    danger α scale (logRad + supportLog S w)
      ≤ danger α scale logRad - α * ((S.card : ℝ) * log2 3) :=
  danger_after_adding_support_le_by_card (S := S) (w := w) hα hw

end

end Note
end ABD
