import ABD.ABD2.Regime.E.Entrance

namespace ABD2
namespace ABCTriple

/-- D1 Stage-3 estimate goal.

This is the first genuinely E-level D1 target: it asks not only for a two-sided
separate-preimage cost witness, but also for the concrete rational power-saving
acceptance inequalities for its bound. -/
def D1PowerSavingEstimate
    (T : ABCTriple) (_P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  ∃ t B : ℤ,
    0 ≤ B ∧
    B ^ data.N < ((T.c : ℤ) ^ data.M) ∧
    T.TwoSidedSeparatePreimageCostAtMost t B

/-- D2 Stage-3 estimate goal.

This is the one-sided forced-lift analogue of `D1PowerSavingEstimate`, specialized
to the coordinate gauge. -/
def D2PowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  ∃ B : ℤ,
    0 ≤ B ∧
    B ^ data.N < ((T.c : ℤ) ^ data.M) ∧
    T.GaugeOneSidedForcedCostAtMost P T.coordinateGauge B

/-- Branch-level Stage-3 coverage goal.

For the current E entrance, it is enough to prove either the D1 power-saving
estimate or the D2 power-saving estimate.  Later files can refine this by adding
actual branch hypotheses and proving that the appropriate side applies. -/
def BranchPowerSavingCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.D1PowerSavingEstimate P data ∨ T.D2PowerSavingEstimate P data

/-- A D1 Stage-3 estimate enters the coordinate-gauge E entrance. -/
theorem eCoordinateGaugeEntrance_of_D1PowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.D1PowerSavingEstimate P data) :
    T.ECoordinateGaugeEntrance P data := by
  rcases h with ⟨t, B, hBnonneg, hpow, hcost⟩
  exact T.eCoordinateGaugeEntrance_of_D1_rationalPowerSaving P data
    hBnonneg hpow hcost

/-- A D2 Stage-3 estimate enters the coordinate-gauge E entrance. -/
theorem eCoordinateGaugeEntrance_of_D2PowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.D2PowerSavingEstimate P data) :
    T.ECoordinateGaugeEntrance P data := by
  rcases h with ⟨B, hBnonneg, hpow, hcost⟩
  exact T.eCoordinateGaugeEntrance_of_D2_rationalPowerSaving P data
    hBnonneg hpow hcost

/-- Branch-level Stage-3 coverage enters the coordinate-gauge E entrance. -/
theorem eCoordinateGaugeEntrance_of_BranchPowerSavingCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.BranchPowerSavingCoverage P data) :
    T.ECoordinateGaugeEntrance P data := by
  rcases h with hD1 | hD2
  · exact T.eCoordinateGaugeEntrance_of_D1PowerSavingEstimate P data hD1
  · exact T.eCoordinateGaugeEntrance_of_D2PowerSavingEstimate P data hD2

/-- A D1 Stage-3 estimate gives the coordinate-gauge power-saving candidate. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_D1PowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (h : T.D1PowerSavingEstimate P data) :
    T.HasPowerSavingCandidate T.coordinateGauge (T.rationalPowerSavingRegime data) := by
  exact T.hasPowerSavingCandidate_coordinateGauge_of_EEntrance P data hblocks hc
    (T.eCoordinateGaugeEntrance_of_D1PowerSavingEstimate P data h)

/-- A D2 Stage-3 estimate gives the coordinate-gauge power-saving candidate. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_D2PowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (h : T.D2PowerSavingEstimate P data) :
    T.HasPowerSavingCandidate T.coordinateGauge (T.rationalPowerSavingRegime data) := by
  exact T.hasPowerSavingCandidate_coordinateGauge_of_EEntrance P data hblocks hc
    (T.eCoordinateGaugeEntrance_of_D2PowerSavingEstimate P data h)

/-- Branch-level Stage-3 coverage gives the coordinate-gauge power-saving
candidate. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_BranchPowerSavingCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (h : T.BranchPowerSavingCoverage P data) :
    T.HasPowerSavingCandidate T.coordinateGauge (T.rationalPowerSavingRegime data) := by
  exact T.hasPowerSavingCandidate_coordinateGauge_of_EEntrance P data hblocks hc
    (T.eCoordinateGaugeEntrance_of_BranchPowerSavingCoverage P data h)

end ABCTriple
end ABD2
