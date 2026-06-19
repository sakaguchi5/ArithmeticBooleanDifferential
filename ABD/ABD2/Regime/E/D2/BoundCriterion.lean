import ABD.ABD2.Regime.E.Stage3Goals

namespace ABD2
namespace ABCTriple

/-- Fixed-bound D2 power-saving criterion.

This is the non-existential core of `D2PowerSavingEstimate`: a chosen bound `B`
must satisfy the rational power-saving inequality and carry a coordinate-gauge
one-sided forced-lift cost witness. -/
def D2PowerSavingBoundCriterion
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (B : ℤ) : Prop :=
  0 ≤ B ∧
    B ^ data.N < ((T.c : ℤ) ^ data.M) ∧
    T.GaugeOneSidedForcedCostAtMost P T.coordinateGauge B

/-- The fixed-bound D2 criterion is exactly its three component conditions. -/
theorem d2PowerSavingBoundCriterion_iff
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (B : ℤ) :
    T.D2PowerSavingBoundCriterion P data B ↔
      0 ≤ B ∧
        B ^ data.N < ((T.c : ℤ) ^ data.M) ∧
        T.GaugeOneSidedForcedCostAtMost P T.coordinateGauge B := by
  rfl

/-- Constructor for the fixed-bound D2 power-saving criterion. -/
theorem d2PowerSavingBoundCriterion_of_components
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.GaugeOneSidedForcedCostAtMost P T.coordinateGauge B) :
    T.D2PowerSavingBoundCriterion P data B := by
  exact ⟨hBnonneg, hpow, hcost⟩

/-- Forget the fixed-bound packaging and recover the E-level existential D2 goal. -/
theorem d2PowerSavingEstimate_of_boundCriterion
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {B : ℤ}
    (h : T.D2PowerSavingBoundCriterion P data B) :
    T.D2PowerSavingEstimate P data := by
  rcases h with ⟨hBnonneg, hpow, hcost⟩
  exact ⟨B, hBnonneg, hpow, hcost⟩

/-- A fixed-bound D2 criterion enters the coordinate-gauge E entrance. -/
theorem eCoordinateGaugeEntrance_of_D2PowerSavingBoundCriterion
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {B : ℤ}
    (h : T.D2PowerSavingBoundCriterion P data B) :
    T.ECoordinateGaugeEntrance P data := by
  exact T.eCoordinateGaugeEntrance_of_D2PowerSavingEstimate P data
    (T.d2PowerSavingEstimate_of_boundCriterion P data h)

/-- A fixed-bound D2 criterion gives the coordinate-gauge power-saving candidate. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_D2PowerSavingBoundCriterion
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    {B : ℤ}
    (h : T.D2PowerSavingBoundCriterion P data B) :
    T.HasPowerSavingCandidate T.coordinateGauge (T.rationalPowerSavingRegime data) := by
  exact T.hasPowerSavingCandidate_coordinateGauge_of_D2PowerSavingEstimate P data
    hblocks hc (T.d2PowerSavingEstimate_of_boundCriterion P data h)

end ABCTriple
end ABD2
