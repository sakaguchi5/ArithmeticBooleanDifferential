import ABD.ABD2.Cost.HardnessNormalForm

namespace ABD2
namespace ABCTriple

/-- Fixed-scalar version of the two-sided AB-cancellation cost.

This is the first D1 refinement: instead of saying merely that some two-sided
cost exists at bound `B`, we expose the scalar cancellation value `t`.
Later refinements can split the single full tangent witness into separate
A- and B-block preimage witnesses. -/
def TwoSidedScalarCancellationCostAtMost
    (T : ABCTriple) (t B : ℤ) : Prop :=
  t ≠ 0 ∧
    ∃ x : T.FullTangent,
      T.ADerivValue x = t ∧
        T.ADerivValue x + T.BDerivValue x = 0 ∧
          T.ABSmallTangent x B

/-- A scalar `t` is two-sided cancellation-compatible if it can be realized
as a nonzero A-value whose A/B values cancel. This forgets the concrete bound. -/
def TwoSidedScalarCancellationCompatible
    (T : ABCTriple) (t : ℤ) : Prop :=
  ∃ B : ℤ, T.TwoSidedScalarCancellationCostAtMost t B

/-- The original C1 cost is exactly the existence of a fixed scalar
cancellation value with the fixed-scalar C1 cost. -/
theorem twoSidedABCancellationCostAtMost_iff_exists_scalarCancellationCostAtMost
    (T : ABCTriple) (B : ℤ) :
    T.TwoSidedABCancellationCostAtMost B ↔
      ∃ t : ℤ, T.TwoSidedScalarCancellationCostAtMost t B := by
  unfold ABCTriple.TwoSidedABCancellationCostAtMost
  unfold ABCTriple.TwoSidedScalarCancellationCostAtMost
  constructor
  · intro h
    rcases h with ⟨x, t, ht_ne, hA, hcancel, hsmall⟩
    exact ⟨t, ht_ne, x, hA, hcancel, hsmall⟩
  · intro h
    rcases h with ⟨t, ht_ne, x, hA, hcancel, hsmall⟩
    exact ⟨x, t, ht_ne, hA, hcancel, hsmall⟩

/-- At a fixed concrete bound, failure of the two-sided C1 cost is equivalent
to failure for every scalar cancellation target. -/
theorem not_twoSidedABCancellationCostAtMost_iff_forall_scalar_not_cost
    (T : ABCTriple) (B : ℤ) :
    ¬ T.TwoSidedABCancellationCostAtMost B ↔
      ∀ t : ℤ, ¬ T.TwoSidedScalarCancellationCostAtMost t B := by
  rw [T.twoSidedABCancellationCostAtMost_iff_exists_scalarCancellationCostAtMost B]
  constructor
  · intro hnot t ht
    exact hnot ⟨t, ht⟩
  · intro hforall h
    rcases h with ⟨t, ht⟩
    exact hforall t ht

/-- D1 hardness as scalar-target failure: every accepted bound fails for every
nonzero scalar cancellation target. -/
theorem twoSidedABCancellationHardness_iff_forall_accepted_forall_scalar_not_cost
    (T : ABCTriple) (R : T.BoundRegime) :
    T.TwoSidedABCancellationHardness R ↔
      ∀ B : ℤ,
        R.accepts B →
          ∀ t : ℤ, ¬ T.TwoSidedScalarCancellationCostAtMost t B := by
  constructor
  · intro hhard B hB
    have hnot : ¬ T.TwoSidedABCancellationCostAtMost B :=
      ((T.twoSidedABCancellationHardness_iff_forall_accepted_not_cost R).mp hhard) B hB
    exact (T.not_twoSidedABCancellationCostAtMost_iff_forall_scalar_not_cost B).mp hnot
  · intro hforall
    apply (T.twoSidedABCancellationHardness_iff_forall_accepted_not_cost R).mpr
    intro B hB
    exact (T.not_twoSidedABCancellationCostAtMost_iff_forall_scalar_not_cost B).mpr (hforall B hB)

/-- A concrete scalar cancellation witness at an accepted bound defeats D1 hardness. -/
theorem not_twoSidedABCancellationHardness_of_scalarCancellationCostAtMost
    (T : ABCTriple) (R : T.BoundRegime) {t B : ℤ}
    (hB : R.accepts B)
    (hcost : T.TwoSidedScalarCancellationCostAtMost t B) :
    ¬ T.TwoSidedABCancellationHardness R := by
  intro hhard
  have hforall :=
    (T.twoSidedABCancellationHardness_iff_forall_accepted_forall_scalar_not_cost R).mp hhard
  exact hforall B hB t hcost

/-- If some scalar cancellation target is realized at an accepted bound,
then the two-sided C1 cost lies in the regime. -/
theorem twoSidedABCancellationCostInRegime_of_scalarCancellationCostAtMost
    (T : ABCTriple) (R : T.BoundRegime) {t B : ℤ}
    (hB : R.accepts B)
    (hcost : T.TwoSidedScalarCancellationCostAtMost t B) :
    T.TwoSidedABCancellationCostInRegime R := by
  exact T.twoSidedABCancellationCostInRegime_of_bound R hB
    ((T.twoSidedABCancellationCostAtMost_iff_exists_scalarCancellationCostAtMost B).mpr ⟨t, hcost⟩)

end ABCTriple
end ABD2
