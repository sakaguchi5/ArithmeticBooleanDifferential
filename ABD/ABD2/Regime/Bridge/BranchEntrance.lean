import ABD.ABD2.Regime.Bridge.D1SectionBridge

namespace ABD2
namespace ABCTriple

/-- Branch-level entrance into the E-roadmap.

The left branch is the D1/two-sided accepted A/B preimage route.  The right
branch is the D2/one-sided accepted forced-lift route in the chosen gauge. -/
def BranchEntrance
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.Regime) : Prop :=
  T.D1AcceptedSeparatePreimage R ∨ T.D2AcceptedForcedLift P G R

/-- Coordinate-gauge branch entrance, the default concrete entrance after the D1
section bridge has been discharged. -/
abbrev CoordinateGaugeBranchEntrance
    (T : ABCTriple) (P : T.CImageProfile) (R : T.Regime) : Prop :=
  T.BranchEntrance P T.coordinateGauge R

/-- Put a D1 accepted witness into the branch entrance. -/
theorem branchEntrance_of_D1AcceptedSeparatePreimage
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) {R : T.Regime}
    (hD1 : T.D1AcceptedSeparatePreimage R) :
    T.BranchEntrance P G R := by
  exact Or.inl hD1

/-- Put a D2 accepted witness into the branch entrance. -/
theorem branchEntrance_of_D2AcceptedForcedLift
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) {R : T.Regime}
    (hD2 : T.D2AcceptedForcedLift P G R) :
    T.BranchEntrance P G R := by
  exact Or.inr hD2

/-- Generic branch entrance gives a gauge candidate once the two-sided section
bridge is available for the chosen gauge. -/
theorem hasGaugeCandidateInRegime_of_branchEntrance
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.Regime)
    (hblocks : T.SupportBlocksDecompose)
    (hbridge : T.TwoSidedSectionBridge G)
    (h : T.BranchEntrance P G R) :
    T.HasGaugeCandidateInRegime G R := by
  rcases h with hD1 | hD2
  · exact T.hasGaugeCandidateInRegime_of_D1AcceptedSeparatePreimage G R
      hblocks hbridge hD1
  · exact T.hasGaugeCandidateInRegime_of_D2AcceptedForcedLift P G R hD2

/-- Generic branch entrance gives a power-saving candidate in a power-saving
regime once the two-sided section bridge is available for the chosen gauge. -/
theorem hasPowerSavingCandidate_of_branchEntrance
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.PowerSavingRegime)
    (hblocks : T.SupportBlocksDecompose)
    (hbridge : T.TwoSidedSectionBridge G)
    (h : T.BranchEntrance P G R) :
    T.HasPowerSavingCandidate G R := by
  exact T.hasPowerSavingCandidate_of_D1_or_D2Accepted P G R hblocks hbridge h

/-- Coordinate-gauge branch entrance gives a gauge candidate in any regime.  The
D1 section bridge is supplied by `D1SectionBridge.lean`. -/
theorem hasGaugeCandidateInRegime_coordinateGauge_of_branchEntrance
    (T : ABCTriple) (P : T.CImageProfile) (R : T.Regime)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (h : T.CoordinateGaugeBranchEntrance P R) :
    T.HasGaugeCandidateInRegime T.coordinateGauge R := by
  exact T.hasGaugeCandidateInRegime_of_branchEntrance P T.coordinateGauge R
    hblocks (T.twoSidedSectionBridge_coordinateGauge hblocks hc) h

/-- Coordinate-gauge branch entrance gives a power-saving candidate in a
power-saving regime. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_branchEntrance
    (T : ABCTriple) (P : T.CImageProfile) (R : T.PowerSavingRegime)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (h : T.CoordinateGaugeBranchEntrance P R) :
    T.HasPowerSavingCandidate T.coordinateGauge R := by
  exact T.hasPowerSavingCandidate_coordinateGauge_of_D1_or_D2Accepted P R
    hblocks hc h

/-- Stage 0, D1 side: any independent A/B preimage cost enters the accept-all
branch entrance. -/
theorem coordinateGaugeBranchEntrance_acceptAll_of_D1Cost
    (T : ABCTriple) (P : T.CImageProfile) {t B : ℤ}
    (hcost : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.CoordinateGaugeBranchEntrance P T.acceptAllRegime := by
  exact Or.inl (T.d1AcceptedSeparatePreimage_acceptAll hcost)

/-- Stage 0, D2 side: any coordinate-gauge one-sided forced cost enters the
accept-all branch entrance. -/
theorem coordinateGaugeBranchEntrance_acceptAll_of_D2Cost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (hcost : T.GaugeOneSidedForcedCostAtMost P T.coordinateGauge B) :
    T.CoordinateGaugeBranchEntrance P T.acceptAllRegime := by
  exact Or.inr (T.oneSidedForcedCostInRegime_acceptAll P T.coordinateGauge hcost)

/-- Stage 1, D1 side: a preimage cost at the exact distinguished bound enters the
exact-bound branch entrance. -/
theorem coordinateGaugeBranchEntrance_exactBound_of_D1Cost
    (T : ABCTriple) (P : T.CImageProfile) {t B₀ : ℤ}
    (hcost : T.TwoSidedSeparatePreimageCostAtMost t B₀) :
    T.CoordinateGaugeBranchEntrance P (T.exactBoundRegime B₀) := by
  exact Or.inl (T.d1AcceptedSeparatePreimage_exactBound hcost)

/-- Stage 1, D2 side: a coordinate-gauge one-sided forced cost at the exact
bound enters the exact-bound branch entrance. -/
theorem coordinateGaugeBranchEntrance_exactBound_of_D2Cost
    (T : ABCTriple) (P : T.CImageProfile) {B₀ : ℤ}
    (hcost : T.GaugeOneSidedForcedCostAtMost P T.coordinateGauge B₀) :
    T.CoordinateGaugeBranchEntrance P (T.exactBoundRegime B₀) := by
  exact Or.inr (T.oneSidedForcedCostInRegime_exactBound P T.coordinateGauge hcost)

/-- Stage 2, D1 side: a preimage cost at `B` enters an upper-bound branch entrance
when `B ≤ B₀`. -/
theorem coordinateGaugeBranchEntrance_upperBound_of_D1Cost
    (T : ABCTriple) (P : T.CImageProfile) {t B B₀ : ℤ}
    (hB : B ≤ B₀)
    (hcost : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.CoordinateGaugeBranchEntrance P (T.upperBoundRegime B₀) := by
  exact Or.inl (T.d1AcceptedSeparatePreimage_upperBound hB hcost)

/-- Stage 2, D2 side: a coordinate-gauge one-sided forced cost at `B` enters an
upper-bound branch entrance when `B ≤ B₀`. -/
theorem coordinateGaugeBranchEntrance_upperBound_of_D2Cost
    (T : ABCTriple) (P : T.CImageProfile) {B B₀ : ℤ}
    (hB : B ≤ B₀)
    (hcost : T.GaugeOneSidedForcedCostAtMost P T.coordinateGauge B) :
    T.CoordinateGaugeBranchEntrance P (T.upperBoundRegime B₀) := by
  exact Or.inr (T.oneSidedForcedCostInRegime_upperBound P T.coordinateGauge hB hcost)

/-- Stage 3, D1 side: a preimage cost at a rational power-saving bound enters the
rational-power-saving branch entrance. -/
theorem coordinateGaugeBranchEntrance_rationalPowerSaving_of_D1Cost
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {t B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.CoordinateGaugeBranchEntrance P (T.rationalPowerSavingRegime data) := by
  exact Or.inl
    (T.d1AcceptedSeparatePreimage_rationalPowerSaving data hBnonneg hpow hcost)

/-- Stage 3, D2 side: a coordinate-gauge one-sided forced cost at a rational
power-saving bound enters the rational-power-saving branch entrance. -/
theorem coordinateGaugeBranchEntrance_rationalPowerSaving_of_D2Cost
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.GaugeOneSidedForcedCostAtMost P T.coordinateGauge B) :
    T.CoordinateGaugeBranchEntrance P (T.rationalPowerSavingRegime data) := by
  exact Or.inr
    (T.oneSidedForcedCostInRegime_rationalPowerSaving P T.coordinateGauge data
      hBnonneg hpow hcost)

end ABCTriple
end ABD2
