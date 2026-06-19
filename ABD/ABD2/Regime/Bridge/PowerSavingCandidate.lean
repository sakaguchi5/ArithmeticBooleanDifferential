import ABD.ABD2.Regime.Bridge.CostInRegime

namespace ABD2
namespace ABCTriple

/-- A bridge from the two-sided C1 cost predicate back to a small strict candidate
in a chosen gauge.

This is intentionally kept as a separate hypothesis: the two-sided cost layer
records AB-cancellation only, while the section bridge explains how that cost is
realized as a full gauge-small strict candidate. -/
def TwoSidedSectionBridge
    (T : ABCTriple) (G : T.Gauge) : Prop :=
  ∀ {B : ℤ},
    T.TwoSidedABCancellationCostAtMost B →
      T.HasSmallStrictCandidateWith G B

/-- The two-sided section bridge turns a two-sided in-regime cost into a gauge
candidate in the same regime. -/
theorem hasGaugeCandidateInRegime_of_twoSidedABCancellationCostInRegime
    (T : ABCTriple) (G : T.Gauge) (R : T.Regime)
    (hbridge : T.TwoSidedSectionBridge G)
    (hcost : T.TwoSidedABCancellationCostInRegime R) :
    T.HasGaugeCandidateInRegime G R := by
  rcases hcost with ⟨B, hB, hcostB⟩
  exact T.hasGaugeCandidateInRegime_of_bound G R hB (hbridge hcostB)

/-- In a power-saving regime, the two-sided section bridge turns two-sided
in-regime cost into a power-saving candidate. -/
theorem hasPowerSavingCandidate_of_twoSidedABCancellationCostInRegime
    (T : ABCTriple) (G : T.Gauge) (R : T.PowerSavingRegime)
    (hbridge : T.TwoSidedSectionBridge G)
    (hcost : T.TwoSidedABCancellationCostInRegime R) :
    T.HasPowerSavingCandidate G R := by
  exact T.hasGaugeCandidateInRegime_of_twoSidedABCancellationCostInRegime G R
    hbridge hcost

/-- D1 accepted separate preimages give a gauge candidate once the support-block
preimage glue and the two-sided section bridge are available. -/
theorem hasGaugeCandidateInRegime_of_D1AcceptedSeparatePreimage
    (T : ABCTriple) (G : T.Gauge) (R : T.Regime)
    (hblocks : T.SupportBlocksDecompose)
    (hbridge : T.TwoSidedSectionBridge G)
    (hD1 : T.D1AcceptedSeparatePreimage R) :
    T.HasGaugeCandidateInRegime G R := by
  exact T.hasGaugeCandidateInRegime_of_twoSidedABCancellationCostInRegime G R
    hbridge
    (T.twoSidedABCancellationCostInRegime_of_D1AcceptedSeparatePreimage R hblocks hD1)

/-- In a power-saving regime, D1 accepted separate preimages give a power-saving
candidate once the support-block preimage glue and the two-sided section bridge
are available. -/
theorem hasPowerSavingCandidate_of_D1AcceptedSeparatePreimage
    (T : ABCTriple) (G : T.Gauge) (R : T.PowerSavingRegime)
    (hblocks : T.SupportBlocksDecompose)
    (hbridge : T.TwoSidedSectionBridge G)
    (hD1 : T.D1AcceptedSeparatePreimage R) :
    T.HasPowerSavingCandidate G R := by
  exact T.hasGaugeCandidateInRegime_of_D1AcceptedSeparatePreimage G R
    hblocks hbridge hD1

/-- D2 accepted forced lift is exactly the existing one-sided forced cost in the
chosen regime, so it already routes to a gauge candidate. -/
theorem hasGaugeCandidateInRegime_of_D2AcceptedForcedLift
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.Regime)
    (hD2 : T.D2AcceptedForcedLift P G R) :
    T.HasGaugeCandidateInRegime G R := by
  exact T.hasGaugeCandidateInRegime_of_oneSidedForcedCostInRegime P G R hD2

/-- In a power-saving regime, D2 accepted forced lift gives a power-saving
candidate. -/
theorem hasPowerSavingCandidate_of_D2AcceptedForcedLift
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.PowerSavingRegime)
    (hD2 : T.D2AcceptedForcedLift P G R) :
    T.HasPowerSavingCandidate G R := by
  exact T.hasPowerSavingCandidate_of_oneSidedForcedCostInRegime P G R hD2

/-- Branch-level E entrance: either D1 or D2 accepted cost gives a power-saving
candidate.  The D1 side needs the explicit two-sided section bridge; the D2 side
already carries a full forced lift. -/
theorem hasPowerSavingCandidate_of_D1_or_D2Accepted
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.PowerSavingRegime)
    (hblocks : T.SupportBlocksDecompose)
    (hbridge : T.TwoSidedSectionBridge G)
    (h : T.D1AcceptedSeparatePreimage R ∨ T.D2AcceptedForcedLift P G R) :
    T.HasPowerSavingCandidate G R := by
  rcases h with hD1 | hD2
  · exact T.hasPowerSavingCandidate_of_D1AcceptedSeparatePreimage G R
      hblocks hbridge hD1
  · exact T.hasPowerSavingCandidate_of_D2AcceptedForcedLift P G R hD2

end ABCTriple
end ABD2
