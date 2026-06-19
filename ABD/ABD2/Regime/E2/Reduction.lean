import ABD.ABD2.Regime.E2.Failure

namespace ABD2
namespace ABCTriple

/-- E2 common scalar coverage enters the existing coordinate-gauge E entrance. -/
theorem eCoordinateGaugeEntrance_of_e2CommonScalarCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2CommonScalarCoverage P data) :
    T.ECoordinateGaugeEntrance P data := by
  exact T.eCoordinateGaugeEntrance_of_BranchPowerSavingCoverage P data
    (T.branchPowerSavingCoverage_of_e2CommonScalarCoverage P data h)

/-- E2 common scalar coverage gives the coordinate-gauge power-saving candidate. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_e2CommonScalarCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (h : T.E2CommonScalarCoverage P data) :
    T.HasPowerSavingCandidate T.coordinateGauge (T.rationalPowerSavingRegime data) := by
  exact T.hasPowerSavingCandidate_coordinateGauge_of_BranchPowerSavingCoverage
    P data hblocks hc
    (T.branchPowerSavingCoverage_of_e2CommonScalarCoverage P data h)

/-- A fixed D1 common scalar witness gives the coordinate-gauge power-saving
candidate. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_d1CommonScalarCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    {t B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.D1CommonScalarCostAtMost t B) :
    T.HasPowerSavingCandidate T.coordinateGauge (T.rationalPowerSavingRegime data) := by
  exact T.hasPowerSavingCandidate_coordinateGauge_of_e2CommonScalarCoverage
    P data hblocks hc
    (T.e2CommonScalarCoverage_of_d1CommonScalarCostAtMost P data
      hBnonneg hpow hcost)

/-- A fixed D2 common scalar witness gives the coordinate-gauge power-saving
candidate. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_d2CommonScalarCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    {t B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.GaugeOneSidedCommonScalarCostAtMost P T.coordinateGauge t B) :
    T.HasPowerSavingCandidate T.coordinateGauge (T.rationalPowerSavingRegime data) := by
  exact T.hasPowerSavingCandidate_coordinateGauge_of_e2CommonScalarCoverage
    P data hblocks hc
    (T.e2CommonScalarCoverage_of_d2CommonScalarCostAtMost P data
      hBnonneg hpow hcost)

end ABCTriple
end ABD2
