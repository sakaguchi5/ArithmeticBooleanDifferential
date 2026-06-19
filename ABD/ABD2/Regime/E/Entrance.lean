import ABD.ABD2.Regime.Bridge.BranchEntrance

namespace ABD2
namespace ABCTriple

/-- E-level entrance for the default coordinate gauge.

At E we no longer treat acceptance as a bare abstract hypothesis: this entrance
uses the concrete rational power-saving regime `B^N < c^M` packaged by
`RationalPowerSavingData`. -/
abbrev ECoordinateGaugeEntrance
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.CoordinateGaugeBranchEntrance P (T.rationalPowerSavingRegime data)

/-- The E entrance is just the Stage-3 coordinate-gauge branch entrance. -/
theorem eCoordinateGaugeEntrance_iff
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.ECoordinateGaugeEntrance P data ↔
      T.CoordinateGaugeBranchEntrance P (T.rationalPowerSavingRegime data) := by
  rfl

/-- D1 route into E: a two-sided separate-preimage cost whose bound satisfies the
rational power-saving inequality enters the coordinate-gauge E entrance. -/
theorem eCoordinateGaugeEntrance_of_D1_rationalPowerSaving
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {t B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.ECoordinateGaugeEntrance P data := by
  exact T.coordinateGaugeBranchEntrance_rationalPowerSaving_of_D1Cost P data
    hBnonneg hpow hcost

/-- D2 route into E: a coordinate-gauge one-sided forced cost whose bound satisfies
the rational power-saving inequality enters the coordinate-gauge E entrance. -/
theorem eCoordinateGaugeEntrance_of_D2_rationalPowerSaving
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.GaugeOneSidedForcedCostAtMost P T.coordinateGauge B) :
    T.ECoordinateGaugeEntrance P data := by
  exact T.coordinateGaugeBranchEntrance_rationalPowerSaving_of_D2Cost P data
    hBnonneg hpow hcost

/-- Once the E entrance is established, the existing branch bridge produces a
coordinate-gauge power-saving candidate. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_EEntrance
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (hE : T.ECoordinateGaugeEntrance P data) :
    T.HasPowerSavingCandidate T.coordinateGauge (T.rationalPowerSavingRegime data) := by
  exact T.hasPowerSavingCandidate_coordinateGauge_of_branchEntrance P
    (T.rationalPowerSavingRegime data) hblocks hc hE

/-- Direct D1 E theorem: a rational power-saving D1 cost gives a coordinate-gauge
power-saving candidate. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_D1_rationalPowerSaving
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    {t B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.HasPowerSavingCandidate T.coordinateGauge (T.rationalPowerSavingRegime data) := by
  exact T.hasPowerSavingCandidate_coordinateGauge_of_EEntrance P data hblocks hc
    (T.eCoordinateGaugeEntrance_of_D1_rationalPowerSaving P data
      hBnonneg hpow hcost)

/-- Direct D2 E theorem: a rational power-saving D2 cost gives a coordinate-gauge
power-saving candidate. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_D2_rationalPowerSaving
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    {B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.GaugeOneSidedForcedCostAtMost P T.coordinateGauge B) :
    T.HasPowerSavingCandidate T.coordinateGauge (T.rationalPowerSavingRegime data) := by
  exact T.hasPowerSavingCandidate_coordinateGauge_of_EEntrance P data hblocks hc
    (T.eCoordinateGaugeEntrance_of_D2_rationalPowerSaving P data
      hBnonneg hpow hcost)

end ABCTriple
end ABD2
