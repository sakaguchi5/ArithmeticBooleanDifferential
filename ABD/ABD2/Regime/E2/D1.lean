import ABD.ABD2.Regime.E2.CommonScalar

namespace ABD2
namespace ABCTriple

/-- E2 D1 common scalar cost.

D1 is the common scalar problem for the A/B pair with right target `-t`:
A realizes `t`, B realizes `-t`, and the two preimage bounds are max-aggregated.
-/
def D1CommonScalarCostAtMost
    (T : ABCTriple) (t B : ℤ) : Prop :=
  CommonScalarPreimageCostAtMost
    T.APreimageCostAtMost
    T.BPreimageCostAtMost
    (fun t => -t)
    t B

/-- D1 common scalar cost is definitionally the existing D1 separate-preimage
cost. -/
theorem d1CommonScalarCostAtMost_iff_twoSidedSeparatePreimageCostAtMost
    (T : ABCTriple) (t B : ℤ) :
    T.D1CommonScalarCostAtMost t B ↔
      T.TwoSidedSeparatePreimageCostAtMost t B := by
  rfl

/-- Existing D1 separate-preimage cost rephrased as the E2 common scalar cost. -/
theorem d1CommonScalarCostAtMost_of_twoSidedSeparatePreimageCostAtMost
    (T : ABCTriple) {t B : ℤ}
    (h : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.D1CommonScalarCostAtMost t B := by
  exact (T.d1CommonScalarCostAtMost_iff_twoSidedSeparatePreimageCostAtMost t B).2 h

/-- E2 common scalar D1 cost rephrased back as the existing D1 separate-preimage
cost. -/
theorem twoSidedSeparatePreimageCostAtMost_of_d1CommonScalarCostAtMost
    (T : ABCTriple) {t B : ℤ}
    (h : T.D1CommonScalarCostAtMost t B) :
    T.TwoSidedSeparatePreimageCostAtMost t B := by
  exact (T.d1CommonScalarCostAtMost_iff_twoSidedSeparatePreimageCostAtMost t B).1 h

/-- E2 D1 power-saving estimate.

This is the same goal as `D1PowerSavingEstimate`, but stated through the common
scalar normalization. -/
def D1CommonScalarPowerSavingEstimate
    (T : ABCTriple) (_P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  CommonScalarPowerSavingEstimate T
    T.APreimageCostAtMost
    T.BPreimageCostAtMost
    (fun t => -t)
    data

/-- The E2 D1 reformulation is equivalent to the existing E/D1 Stage-3 goal. -/
theorem d1CommonScalarPowerSavingEstimate_iff_d1PowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.D1CommonScalarPowerSavingEstimate P data ↔
      T.D1PowerSavingEstimate P data := by
  rfl

/-- Convert the E2 D1 formulation to the existing E/D1 Stage-3 goal. -/
theorem d1PowerSavingEstimate_of_d1CommonScalarPowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.D1CommonScalarPowerSavingEstimate P data) :
    T.D1PowerSavingEstimate P data := by
  exact (T.d1CommonScalarPowerSavingEstimate_iff_d1PowerSavingEstimate P data).1 h

/-- Convert the existing E/D1 Stage-3 goal to the E2 D1 formulation. -/
theorem d1CommonScalarPowerSavingEstimate_of_d1PowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.D1PowerSavingEstimate P data) :
    T.D1CommonScalarPowerSavingEstimate P data := by
  exact (T.d1CommonScalarPowerSavingEstimate_iff_d1PowerSavingEstimate P data).2 h

/-- A single fixed D1 common scalar witness gives the existing D1 Stage-3 goal. -/
theorem d1PowerSavingEstimate_of_d1CommonScalarCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {t B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.D1CommonScalarCostAtMost t B) :
    T.D1PowerSavingEstimate P data := by
  exact ⟨t, B, hBnonneg, hpow,
    T.twoSidedSeparatePreimageCostAtMost_of_d1CommonScalarCostAtMost hcost⟩

end ABCTriple
end ABD2
