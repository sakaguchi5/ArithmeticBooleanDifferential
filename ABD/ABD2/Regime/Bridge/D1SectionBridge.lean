import ABD.ABD2.Regime.Bridge.PowerSavingCandidate

namespace ABD2
namespace ABCTriple

/-- The C-mask of the AB part is zero under a support-block decomposition.

This is the Boolean fact behind the D1 section bridge: a two-sided A/B
cancellation witness is turned into a full tangent by keeping only its A/B part,
so the C-linear form of that glued point is zero. -/
theorem maskC_ABPart_eq_zero_of_supportBlocksDecompose
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (x : T.FullTangent) :
    T.maskC (T.ABPart x) = 0 := by
  funext p
  by_cases hpC : p.1 ∈ T.supportC
  · have hpA : p.1 ∉ T.supportA := by
      intro hpA
      exact Finset.disjoint_left.mp hblocks.disjAC hpA hpC
    have hpB : p.1 ∉ T.supportB := by
      intro hpB
      exact Finset.disjoint_left.mp hblocks.disjBC hpB hpC
    simp [ABCTriple.maskC, ABCTriple.ABPart, ABCTriple.maskA,
      ABCTriple.maskB, supportMask, hpC, hpA, hpB]
  · simp [ABCTriple.maskC, supportMask, hpC]

/-- The C-linear form vanishes on the AB part under a support-block decomposition. -/
theorem cLinearForm_ABPart_eq_zero_of_supportBlocksDecompose
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (x : T.FullTangent) :
    T.cLinearForm (T.ABPart x) = 0 := by
  unfold ABCTriple.cLinearForm
  rw [T.maskC_ABPart_eq_zero_of_supportBlocksDecompose hblocks x]
  simp

/-- The AB part is a C-lift of a target-zero seed.

If the seed has AB target zero, then the AB projection preserves the A/B masks and
has zero C-linear form, hence it is a concrete C-lift of the seed. -/
theorem hasCLift_ABPart_of_abTarget_eq_zero
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    {x : T.FullTangent}
    (htarget : T.abTarget x = 0) :
    T.HasCLift x (T.ABPart x) := by
  refine
    { maskA_eq := ?_
      maskB_eq := ?_
      c_balance := ?_ }
  · simpa [ABCTriple.ABPart] using
      T.maskA_maskA_add_maskB_eq_maskA hblocks x x
  · simpa [ABCTriple.ABPart] using
      T.maskB_maskA_add_maskB_eq_maskB hblocks x x
  · rw [T.cLinearForm_ABPart_eq_zero_of_supportBlocksDecompose hblocks x]
    exact htarget.symm

/-- D1 section bridge at a concrete bound, in the coordinate gauge.

A two-sided AB-cancellation cost witness carries a nonzero scalar `t`, internal
A/B cancellation, and AB-smallness.  Keeping only its AB part gives a zero C-lift;
the nonzero scalar and `c ≠ 0` give Wronskian nondegeneracy. -/
theorem hasSmallStrictCandidateWith_coordinateGauge_of_twoSidedABCancellationCostAtMost
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    {B : ℤ}
    (hcost : T.TwoSidedABCancellationCostAtMost B) :
    T.HasSmallStrictCandidateWith T.coordinateGauge B := by
  rcases hcost with ⟨x, t, ht_ne, hA, hcancel, hsmall⟩
  let lift : T.FullTangent := T.ABPart x
  have htarget : T.abTarget x = 0 := by
    rw [T.abTarget_eq_ADerivValue_add_BDerivValue x]
    exact hcancel
  have hBvalue : T.BDerivValue x = -t := by
    have h : T.BDerivValue x + t = 0 := by
      simpa [hA, add_comm] using hcancel
    exact eq_neg_of_add_eq_zero_left h
  have hDa : formalDeriv T.support x T.a = t := by
    simpa [ABCTriple.ADerivValue] using hA
  have hDb : formalDeriv T.support x T.b = -t := by
    simpa [ABCTriple.BDerivValue] using hBvalue
  have hWne : T.Wronskian x ≠ 0 :=
    T.Wronskian_ne_zero_of_opposite_formalDeriv x t hc ht_ne hDa hDb
  have hnd : x ∉ T.ABWronskianKernel := by
    intro hxker
    exact hWne ((T.mem_ABWronskianKernel_iff x).1 hxker)
  have hclift : T.HasCLift x lift := by
    simpa [lift] using T.hasCLift_ABPart_of_abTarget_eq_zero hblocks htarget
  have hstrict : T.StrictCandidate lift :=
    T.strictCandidate_of_goodSeed_and_cLift x lift hnd hclift
  have hsmallLift : T.coordinateGauge.small lift B := by
    simpa [lift, ABCTriple.coordinateGauge, ABCTriple.ABSmallTangent] using hsmall
  exact ⟨lift, hstrict, hsmallLift⟩

/-- The D1 section bridge for the coordinate gauge.

This removes the abstract `TwoSidedSectionBridge` hypothesis on the D1 side when
we work with the existing coordinatewise gauge. -/
theorem twoSidedSectionBridge_coordinateGauge
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0) :
    T.TwoSidedSectionBridge T.coordinateGauge := by
  intro B hcost
  exact T.hasSmallStrictCandidateWith_coordinateGauge_of_twoSidedABCancellationCostAtMost
    hblocks hc hcost

/-- D1 accepted separate preimages give a coordinate-gauge candidate in any regime. -/
theorem hasGaugeCandidateInRegime_coordinateGauge_of_D1AcceptedSeparatePreimage
    (T : ABCTriple) (R : T.Regime)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (hD1 : T.D1AcceptedSeparatePreimage R) :
    T.HasGaugeCandidateInRegime T.coordinateGauge R := by
  exact T.hasGaugeCandidateInRegime_of_D1AcceptedSeparatePreimage T.coordinateGauge R
    hblocks (T.twoSidedSectionBridge_coordinateGauge hblocks hc) hD1

/-- In a power-saving regime, D1 accepted separate preimages give a
coordinate-gauge power-saving candidate. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_D1AcceptedSeparatePreimage
    (T : ABCTriple) (R : T.PowerSavingRegime)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (hD1 : T.D1AcceptedSeparatePreimage R) :
    T.HasPowerSavingCandidate T.coordinateGauge R := by
  exact T.hasPowerSavingCandidate_of_D1AcceptedSeparatePreimage T.coordinateGauge R
    hblocks (T.twoSidedSectionBridge_coordinateGauge hblocks hc) hD1

/-- Coordinate-gauge branch entrance after discharging the D1 section bridge.

The D1 side uses the concrete coordinate-gauge section bridge proved in this
file.  The D2 side already carries a full forced lift. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_D1_or_D2Accepted
    (T : ABCTriple) (P : T.CImageProfile) (R : T.PowerSavingRegime)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (h : T.D1AcceptedSeparatePreimage R ∨
      T.D2AcceptedForcedLift P T.coordinateGauge R) :
    T.HasPowerSavingCandidate T.coordinateGauge R := by
  rcases h with hD1 | hD2
  · exact T.hasPowerSavingCandidate_coordinateGauge_of_D1AcceptedSeparatePreimage R
      hblocks hc hD1
  · exact T.hasPowerSavingCandidate_of_D2AcceptedForcedLift P T.coordinateGauge R hD2

end ABCTriple
end ABD2
