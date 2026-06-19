import ABD.ABD2.Regime.E2.CommonScalar

namespace ABD2
namespace ABCTriple

/-- E2 D2 common scalar witness.

Unlike D1, the one-sided forced route has extra structural data: the active
one-sided seed, the C-lift, the good-base certificate, and the lift relation.
The common scalar `t` is exposed explicitly so D2 can be studied as the same
common-value problem:
  active side produces `t`;
  C side receives `t`.
-/
def GaugeOneSidedCommonScalarCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (t B : ℤ) : Prop :=
  t ≠ 0 ∧
    ∃ seed : T.FullTangent,
    ∃ lift : T.FullTangent,
      T.OneSidedABSupport ∧
        T.GoodBasePoint P seed ∧
          T.HasCLift seed lift ∧
            T.abTarget seed = t ∧
              T.cLinearForm lift = t ∧
                G.small lift B

/-- Constructor for the E2 D2 common scalar witness. -/
theorem gaugeOneSidedCommonScalarCostAtMost_of_components
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    {seed lift : T.FullTangent} {t B : ℤ}
    (ht : t ≠ 0)
    (hside : T.OneSidedABSupport)
    (hgood : T.GoodBasePoint P seed)
    (hclift : T.HasCLift seed lift)
    (htarget : T.abTarget seed = t)
    (hcLinear : T.cLinearForm lift = t)
    (hsmall : G.small lift B) :
    T.GaugeOneSidedCommonScalarCostAtMost P G t B := by
  exact ⟨ht, seed, lift, hside, hgood, hclift, htarget, hcLinear, hsmall⟩

/-- Existing gauge one-sided forced cost is equivalent to existence of an E2
common scalar witness. -/
theorem gaugeOneSidedForcedCostAtMost_iff_exists_commonScalar
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (B : ℤ) :
    T.GaugeOneSidedForcedCostAtMost P G B ↔
      ∃ t : ℤ, T.GaugeOneSidedCommonScalarCostAtMost P G t B := by
  constructor
  · intro h
    rcases h with ⟨seed, lift, t, ht, hside, hgood, hclift,
      htarget, hcLinear, hsmall⟩
    exact ⟨t, ht, seed, lift, hside, hgood, hclift, htarget, hcLinear, hsmall⟩
  · intro h
    rcases h with ⟨t, ht, seed, lift, hside, hgood, hclift,
      htarget, hcLinear, hsmall⟩
    exact ⟨seed, lift, t, ht, hside, hgood, hclift, htarget, hcLinear, hsmall⟩

/-- E2 common scalar witness gives the existing gauge one-sided forced cost. -/
theorem gaugeOneSidedForcedCostAtMost_of_commonScalar
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) {t B : ℤ}
    (h : T.GaugeOneSidedCommonScalarCostAtMost P G t B) :
    T.GaugeOneSidedForcedCostAtMost P G B := by
  exact (T.gaugeOneSidedForcedCostAtMost_iff_exists_commonScalar P G B).2 ⟨t, h⟩

/-- Existing gauge one-sided forced cost exposes a nonzero common scalar. -/
theorem exists_commonScalar_of_gaugeOneSidedForcedCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) {B : ℤ}
    (h : T.GaugeOneSidedForcedCostAtMost P G B) :
    ∃ t : ℤ, T.GaugeOneSidedCommonScalarCostAtMost P G t B := by
  exact (T.gaugeOneSidedForcedCostAtMost_iff_exists_commonScalar P G B).1 h

/-- E2 D2 power-saving estimate.

This is the one-sided forced Stage-3 goal with the hidden forced scalar exposed.
-/
def D2CommonScalarPowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  ∃ t B : ℤ,
    0 ≤ B ∧
      B ^ data.N < ((T.c : ℤ) ^ data.M) ∧
        T.GaugeOneSidedCommonScalarCostAtMost P T.coordinateGauge t B

/-- E2 D2 is equivalent to the existing E/D2 Stage-3 goal. -/
theorem d2CommonScalarPowerSavingEstimate_iff_d2PowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.D2CommonScalarPowerSavingEstimate P data ↔
      T.D2PowerSavingEstimate P data := by
  constructor
  · intro h
    rcases h with ⟨t, B, hBnonneg, hpow, hcost⟩
    exact ⟨B, hBnonneg, hpow,
      T.gaugeOneSidedForcedCostAtMost_of_commonScalar P T.coordinateGauge hcost⟩
  · intro h
    rcases h with ⟨B, hBnonneg, hpow, hcost⟩
    rcases T.exists_commonScalar_of_gaugeOneSidedForcedCostAtMost P T.coordinateGauge hcost with
      ⟨t, hcommon⟩
    exact ⟨t, B, hBnonneg, hpow, hcommon⟩

/-- Convert the E2 D2 formulation to the existing E/D2 Stage-3 goal. -/
theorem d2PowerSavingEstimate_of_d2CommonScalarPowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.D2CommonScalarPowerSavingEstimate P data) :
    T.D2PowerSavingEstimate P data := by
  exact (T.d2CommonScalarPowerSavingEstimate_iff_d2PowerSavingEstimate P data).1 h

/-- Convert the existing E/D2 Stage-3 goal to the E2 D2 formulation. -/
theorem d2CommonScalarPowerSavingEstimate_of_d2PowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.D2PowerSavingEstimate P data) :
    T.D2CommonScalarPowerSavingEstimate P data := by
  exact (T.d2CommonScalarPowerSavingEstimate_iff_d2PowerSavingEstimate P data).2 h

/-- A single fixed D2 common scalar witness gives the existing D2 Stage-3 goal. -/
theorem d2PowerSavingEstimate_of_gaugeOneSidedCommonScalarCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {t B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.GaugeOneSidedCommonScalarCostAtMost P T.coordinateGauge t B) :
    T.D2PowerSavingEstimate P data := by
  exact ⟨B, hBnonneg, hpow,
    T.gaugeOneSidedForcedCostAtMost_of_commonScalar P T.coordinateGauge hcost⟩

end ABCTriple
end ABD2
