import ABD.Note.SupportSafety
import ABD.Note.SupportSafetyNat

/-!
# Support safety: sharper distinct-support lower bounds

The rough theorem counts every new odd support as if it contributed only
`log₂ 3`.  Since a support set has no repeated prime, the sharper lower bound is
obtained by summing the logarithms of the chosen comparison supports, for example
`log₂ 3 + log₂ 5 + log₂ 7 + ...`.

This file formalizes that sharper statement at the log-weight level.  It does
not try to prove inside Lean that the comparison list is literally the first `r`
odd primes.  Instead it proves the reusable theorem: if each support weight is
bounded below by a chosen comparison weight, then the support drop is bounded
below by the sum of those comparison weights.  Instantiating the comparison
weights with `log₂ 3`, `log₂ 5`, `log₂ 7`, ... gives the intended sharp bound.
-/

namespace ABD
namespace Note

/--
Pointwise sharp quantitative bound.

If every new support weight `w i` is at least a chosen lower weight `lower i`,
then the total safety drop is at least `α * supportLog S lower`.

For distinct odd prime supports, `lower` should be the matched list
`log₂ 3`, `log₂ 5`, `log₂ 7`, ... after ordering/matching the support set.
-/
theorem support_drop_lower_bound_by_pointwise_lower
    {ι : Type u} {α : ℝ} {S : Finset ι} {w lower : ι → ℝ}
    (hα : 0 ≤ α)
    (hlower : ∀ i, i ∈ S → lower i ≤ w i) :
    α * supportLog S lower ≤ supportDrop α S w := by
  have hsum : supportLog S lower ≤ supportLog S w := by
    unfold supportLog
    exact Finset.sum_le_sum hlower
  exact mul_le_mul_of_nonneg_left hsum hα

/--
Danger-score version of the pointwise sharp quantitative bound.
-/
theorem danger_after_adding_support_le_by_pointwise_lower
    {ι : Type u} {α scale logRad : ℝ} {S : Finset ι} {w lower : ι → ℝ}
    (hα : 0 ≤ α)
    (hlower : ∀ i, i ∈ S → lower i ≤ w i) :
    danger α scale (logRad + supportLog S w)
      ≤ danger α scale logRad - α * supportLog S lower := by
  have hdrop : α * supportLog S lower ≤ supportDrop α S w :=
    support_drop_lower_bound_by_pointwise_lower
      (S := S) (w := w) (lower := lower) hα hlower
  have hsub :
      danger α scale logRad - supportDrop α S w
        ≤ danger α scale logRad - α * supportLog S lower :=
    sub_le_sub_left hdrop (danger α scale logRad)
  calc
    danger α scale (logRad + supportLog S w)
        = danger α scale logRad - supportDrop α S w :=
          danger_after_adding_support_eq α scale logRad S w
    _ ≤ danger α scale logRad - α * supportLog S lower := hsub

/--
Sharp product-log formulation.

If `L` is any certified lower bound for the total support log, then the support
drop is at least `α * L`.

The intended use is:
`L = log₂ (3 * 5 * 7 * ... * p_r)`.
-/
theorem support_drop_lower_bound_by_total_lower
    {ι : Type u} {α L : ℝ} {S : Finset ι} {w : ι → ℝ}
    (hα : 0 ≤ α)
    (hL : L ≤ supportLog S w) :
    α * L ≤ supportDrop α S w := by
  exact mul_le_mul_of_nonneg_left hL hα

/--
Danger-score version of the sharp product-log formulation.
-/
theorem danger_after_adding_support_le_by_total_lower
    {ι : Type u} {α L scale logRad : ℝ} {S : Finset ι} {w : ι → ℝ}
    (hα : 0 ≤ α)
    (hL : L ≤ supportLog S w) :
    danger α scale (logRad + supportLog S w)
      ≤ danger α scale logRad - α * L := by
  have hdrop : α * L ≤ supportDrop α S w :=
    support_drop_lower_bound_by_total_lower
      (S := S) (w := w) hα hL
  have hsub :
      danger α scale logRad - supportDrop α S w
        ≤ danger α scale logRad - α * L :=
    sub_le_sub_left hdrop (danger α scale logRad)
  calc
    danger α scale (logRad + supportLog S w)
        = danger α scale logRad - supportDrop α S w :=
          danger_after_adding_support_eq α scale logRad S w
    _ ≤ danger α scale logRad - α * L := hsub

/--
A concrete three-support example of the sharper lower bound.

If three selected supports have log-weights at least `log₂ 3`, `log₂ 5`, and
`log₂ 7`, respectively, then the certified lower bound is their sum.  This is a
small concrete model of the general "first odd primes" lower bound.
-/
theorem support_drop_lower_bound_three_distinct_model
    {α w3 w5 w7 : ℝ}
    (hα : 0 ≤ α)
    (h3 : log2 3 ≤ w3)
    (h5 : log2 5 ≤ w5)
    (h7 : log2 7 ≤ w7) :
    α * (log2 3 + log2 5 + log2 7)
      ≤ α * (w3 + w5 + w7) := by
  have hsum : log2 3 + log2 5 + log2 7 ≤ w3 + w5 + w7 := by
    exact add_le_add (add_le_add h3 h5) h7
  exact mul_le_mul_of_nonneg_left hsum hα


end Note
end ABD
