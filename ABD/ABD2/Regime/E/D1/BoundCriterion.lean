import ABD.ABD2.Regime.E.Stage3Goals

namespace ABD2
namespace ABCTriple

/-- Fixed-bound D1 power-saving criterion.

This is the non-existential core of `D1PowerSavingEstimate`: a chosen scalar
`t` and bound `B` must satisfy the rational power-saving inequality and carry a
D1 separate-preimage cost witness. -/
def D1PowerSavingBoundCriterion
    (T : ABCTriple) (_P : T.CImageProfile) (data : RationalPowerSavingData)
    (t B : ℤ) : Prop :=
  0 ≤ B ∧
    B ^ data.N < ((T.c : ℤ) ^ data.M) ∧
    T.TwoSidedSeparatePreimageCostAtMost t B

/-- The fixed-bound D1 criterion is exactly its three component conditions. -/
theorem d1PowerSavingBoundCriterion_iff
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (t B : ℤ) :
    T.D1PowerSavingBoundCriterion P data t B ↔
      0 ≤ B ∧
        B ^ data.N < ((T.c : ℤ) ^ data.M) ∧
        T.TwoSidedSeparatePreimageCostAtMost t B := by
  rfl

/-- Constructor for the fixed-bound D1 power-saving criterion. -/
theorem d1PowerSavingBoundCriterion_of_components
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {t B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.D1PowerSavingBoundCriterion P data t B := by
  exact ⟨hBnonneg, hpow, hcost⟩

/-- Forget the fixed-bound packaging and recover the E-level existential D1 goal. -/
theorem d1PowerSavingEstimate_of_boundCriterion
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {t B : ℤ}
    (h : T.D1PowerSavingBoundCriterion P data t B) :
    T.D1PowerSavingEstimate P data := by
  rcases h with ⟨hBnonneg, hpow, hcost⟩
  exact ⟨t, B, hBnonneg, hpow, hcost⟩

/-- A fixed-bound D1 criterion enters the coordinate-gauge E entrance. -/
theorem eCoordinateGaugeEntrance_of_D1PowerSavingBoundCriterion
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {t B : ℤ}
    (h : T.D1PowerSavingBoundCriterion P data t B) :
    T.ECoordinateGaugeEntrance P data := by
  exact T.eCoordinateGaugeEntrance_of_D1PowerSavingEstimate P data
    (T.d1PowerSavingEstimate_of_boundCriterion P data h)

/-- A fixed-bound D1 criterion gives the coordinate-gauge power-saving candidate. -/
theorem hasPowerSavingCandidate_coordinateGauge_of_D1PowerSavingBoundCriterion
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    {t B : ℤ}
    (h : T.D1PowerSavingBoundCriterion P data t B) :
    T.HasPowerSavingCandidate T.coordinateGauge (T.rationalPowerSavingRegime data) := by
  exact T.hasPowerSavingCandidate_coordinateGauge_of_D1PowerSavingEstimate P data
    hblocks hc (T.d1PowerSavingEstimate_of_boundCriterion P data h)

end ABCTriple
end ABD2
