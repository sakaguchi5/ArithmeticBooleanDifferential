import ABD.ABD2.Cost.TwoSidedPreimageGlue

namespace ABD2
namespace ABCTriple

/-- Max aggregation controls the existing AB-smallness predicate under Boolean
A/B disjointness.

At each coordinate of the AB part, disjointness says that either the A component
or the B component contributes, but not both.  Hence max-style component bounds
control the whole AB projection. -/
theorem twoSidedPreimageAggregateControlsABSmall_max_of_supportBlocksDecompose
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose) :
    T.TwoSidedPreimageAggregateControlsABSmall MaxAgg := by
  intro x BA BB B hsmallA hsmallB hagg
  rcases hagg with ⟨hBA, hBB⟩
  unfold ABCTriple.APreimageSmall at hsmallA
  unfold ABCTriple.BPreimageSmall at hsmallB
  unfold ABCTriple.ABSmallTangent
  unfold ABCTriple.SmallTangent
  intro p
  by_cases hpA : p.1 ∈ T.supportA
  · have hpB : p.1 ∉ T.supportB := by
      intro hpB
      exact Finset.disjoint_left.mp hblocks.disjAB hpA hpB
    have hcoord : T.ABPart x p = T.maskA x p := by
      simp [ABCTriple.ABPart, ABCTriple.maskA, ABCTriple.maskB, supportMask, hpA, hpB]
    have hAcoord := hsmallA p
    rw [hcoord]
    exact ⟨le_trans (neg_le_neg hBA) hAcoord.1, le_trans hAcoord.2 hBA⟩
  · by_cases hpB : p.1 ∈ T.supportB
    · have hcoord : T.ABPart x p = T.maskB x p := by
        simp [ABCTriple.ABPart, ABCTriple.maskA, ABCTriple.maskB, supportMask, hpA, hpB]
      have hBcoord := hsmallB p
      rw [hcoord]
      exact ⟨le_trans (neg_le_neg hBB) hBcoord.1, le_trans hBcoord.2 hBB⟩
    · have hcoord : T.ABPart x p = 0 := by
        simp [ABCTriple.ABPart, ABCTriple.maskA, ABCTriple.maskB, supportMask, hpA, hpB]
      have hAcoord := hsmallA p
      have hmaskA_zero : T.maskA x p = 0 := by
        simp [ABCTriple.maskA, supportMask, hpA]
      have h0leBA : 0 ≤ BA := by
        simpa [hmaskA_zero] using hAcoord.2
      have h0leB : 0 ≤ B := le_trans h0leBA hBA
      rw [hcoord]
      exact ⟨neg_nonpos.mpr h0leB, h0leB⟩

/-- The two bridge principles needed by `TwoSidedPreimage.lean` are both supplied
by a support-block decomposition. -/
theorem twoSidedScalarCancellationCostAtMost_of_separatePreimageCostAtMost_of_supportBlocksDecompose
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose) {t B : ℤ}
    (h : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.TwoSidedScalarCancellationCostAtMost t B := by
  exact T.twoSidedScalarCancellationCostAtMost_of_separatePreimageCostAtMost
    (T.twoSidedPreimageGlue_of_supportBlocksDecompose hblocks)
    (T.twoSidedPreimageAggregateControlsABSmall_max_of_supportBlocksDecompose hblocks)
    h

/-- A concrete independent A/B preimage witness defeats D1 hardness using only the
Boolean support-block decomposition. -/
theorem not_twoSidedABCancellationHardness_of_separatePreimageCostAtMost_of_supportBlocksDecompose
    (T : ABCTriple) (R : T.BoundRegime)
    (hblocks : T.SupportBlocksDecompose) {t B : ℤ}
    (hB : R.accepts B)
    (h : T.TwoSidedSeparatePreimageCostAtMost t B) :
    ¬ T.TwoSidedABCancellationHardness R := by
  exact T.not_twoSidedABCancellationHardness_of_separatePreimageCostAtMost R hB
    (T.twoSidedPreimageGlue_of_supportBlocksDecompose hblocks)
    (T.twoSidedPreimageAggregateControlsABSmall_max_of_supportBlocksDecompose hblocks)
    h

end ABCTriple
end ABD2
