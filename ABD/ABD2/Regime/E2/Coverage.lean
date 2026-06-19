import ABD.ABD2.Regime.E2.D1
import ABD.ABD2.Regime.E2.D2

namespace ABD2
namespace ABCTriple

/-- E2 coverage: either the D1 common scalar reformulation succeeds or the D2
common scalar reformulation succeeds. -/
def E2CommonScalarCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.D1CommonScalarPowerSavingEstimate P data ∨
    T.D2CommonScalarPowerSavingEstimate P data

/-- E2 common scalar coverage is equivalent to the existing E branch coverage. -/
theorem e2CommonScalarCoverage_iff_branchPowerSavingCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2CommonScalarCoverage P data ↔
      T.BranchPowerSavingCoverage P data := by
  constructor
  · intro h
    rcases h with hD1 | hD2
    · exact Or.inl (T.d1PowerSavingEstimate_of_d1CommonScalarPowerSavingEstimate P data hD1)
    · exact Or.inr (T.d2PowerSavingEstimate_of_d2CommonScalarPowerSavingEstimate P data hD2)
  · intro h
    rcases h with hD1 | hD2
    · exact Or.inl (T.d1CommonScalarPowerSavingEstimate_of_d1PowerSavingEstimate P data hD1)
    · exact Or.inr (T.d2CommonScalarPowerSavingEstimate_of_d2PowerSavingEstimate P data hD2)

/-- Existing E branch coverage can be viewed as E2 common scalar coverage. -/
theorem e2CommonScalarCoverage_of_branchPowerSavingCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.BranchPowerSavingCoverage P data) :
    T.E2CommonScalarCoverage P data := by
  exact (T.e2CommonScalarCoverage_iff_branchPowerSavingCoverage P data).2 h

/-- E2 common scalar coverage can be viewed as existing E branch coverage. -/
theorem branchPowerSavingCoverage_of_e2CommonScalarCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2CommonScalarCoverage P data) :
    T.BranchPowerSavingCoverage P data := by
  exact (T.e2CommonScalarCoverage_iff_branchPowerSavingCoverage P data).1 h

/-- Direct D1 entrance into E2 coverage from a fixed common scalar witness. -/
theorem e2CommonScalarCoverage_of_d1CommonScalarCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {t B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.D1CommonScalarCostAtMost t B) :
    T.E2CommonScalarCoverage P data := by
  exact Or.inl
    (commonScalarPowerSavingEstimate_of_bound
      T data hBnonneg hpow hcost)

/-- Direct D2 entrance into E2 coverage from a fixed common scalar witness. -/
theorem e2CommonScalarCoverage_of_d2CommonScalarCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {t B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.GaugeOneSidedCommonScalarCostAtMost P T.coordinateGauge t B) :
    T.E2CommonScalarCoverage P data := by
  exact Or.inr ⟨t, B, hBnonneg, hpow, hcost⟩

end ABCTriple
end ABD2
