import ABD.ABD2.Regime.E2.Failure

namespace ABD2

/-- Universal failure form for a common scalar power-saving estimate.

Instead of saying that no witness exists, this form says that every concrete
common-scalar witness at a nonnegative bound fails the rational power-saving
inequality.  This is the contrapositive-friendly version of the E2 route. -/
def CommonScalarPowerSavingFailure
    (T : ABCTriple)
    (leftCost rightCost : ℤ → ℤ → Prop)
    (rightTarget : ℤ → ℤ)
    (data : ABCTriple.RationalPowerSavingData) : Prop :=
  ∀ t B : ℤ,
    CommonScalarPreimageCostAtMost leftCost rightCost rightTarget t B →
      0 ≤ B →
        ¬ B ^ data.N < ((T.c : ℤ) ^ data.M)

/-- Universal failure is exactly the negation of the existential common scalar
power-saving estimate. -/
theorem commonScalarPowerSavingFailure_iff_not_commonScalarPowerSavingEstimate
    (T : ABCTriple)
    (leftCost rightCost : ℤ → ℤ → Prop)
    (rightTarget : ℤ → ℤ)
    (data : ABCTriple.RationalPowerSavingData) :
    CommonScalarPowerSavingFailure T leftCost rightCost rightTarget data ↔
      ¬ CommonScalarPowerSavingEstimate T leftCost rightCost rightTarget data := by
  constructor
  · intro hfail hest
    rcases hest with ⟨t, B, hBnonneg, hpow, hcost⟩
    exact hfail t B hcost hBnonneg hpow
  · intro hnot t B hcost hBnonneg hpow
    exact hnot ⟨t, B, hBnonneg, hpow, hcost⟩

namespace ABCTriple

/-- D1 failure in E2 normal form: every A/B common-scalar cancellation witness
misses the requested rational power-saving bound. -/
def D1CommonScalarPowerSavingFailure
    (T : ABCTriple) (_P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  CommonScalarPowerSavingFailure T
    T.APreimageCostAtMost
    T.BPreimageCostAtMost
    (fun t => -t)
    data

/-- D1 E2 failure is exactly the negation of the E2 D1 power-saving estimate. -/
theorem d1CommonScalarPowerSavingFailure_iff_not_d1CommonScalarPowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.D1CommonScalarPowerSavingFailure P data ↔
      ¬ T.D1CommonScalarPowerSavingEstimate P data := by
  exact commonScalarPowerSavingFailure_iff_not_commonScalarPowerSavingEstimate
    T T.APreimageCostAtMost T.BPreimageCostAtMost (fun t => -t) data

/-- D1 E2 failure is also the negation of the existing E/D1 Stage-3 goal. -/
theorem d1CommonScalarPowerSavingFailure_iff_not_d1PowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.D1CommonScalarPowerSavingFailure P data ↔
      ¬ T.D1PowerSavingEstimate P data := by
  constructor
  · intro hfail hD1
    have hcommon : T.D1CommonScalarPowerSavingEstimate P data :=
      T.d1CommonScalarPowerSavingEstimate_of_d1PowerSavingEstimate P data hD1
    exact ((T.d1CommonScalarPowerSavingFailure_iff_not_d1CommonScalarPowerSavingEstimate P data).1
      hfail) hcommon
  · intro hnot
    exact (T.d1CommonScalarPowerSavingFailure_iff_not_d1CommonScalarPowerSavingEstimate P data).2
      (fun hcommon => hnot
        (T.d1PowerSavingEstimate_of_d1CommonScalarPowerSavingEstimate P data hcommon))

/-- D2 failure in E2 normal form: every exposed one-sided common-scalar witness
misses the requested rational power-saving bound. -/
def D2CommonScalarPowerSavingFailure
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  ∀ t B : ℤ,
    T.GaugeOneSidedCommonScalarCostAtMost P T.coordinateGauge t B →
      0 ≤ B →
        ¬ B ^ data.N < ((T.c : ℤ) ^ data.M)

/-- D2 E2 failure is exactly the negation of the E2 D2 power-saving estimate. -/
theorem d2CommonScalarPowerSavingFailure_iff_not_d2CommonScalarPowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.D2CommonScalarPowerSavingFailure P data ↔
      ¬ T.D2CommonScalarPowerSavingEstimate P data := by
  constructor
  · intro hfail hest
    rcases hest with ⟨t, B, hBnonneg, hpow, hcost⟩
    exact hfail t B hcost hBnonneg hpow
  · intro hnot t B hcost hBnonneg hpow
    exact hnot ⟨t, B, hBnonneg, hpow, hcost⟩

/-- D2 E2 failure is also the negation of the existing E/D2 Stage-3 goal. -/
theorem d2CommonScalarPowerSavingFailure_iff_not_d2PowerSavingEstimate
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.D2CommonScalarPowerSavingFailure P data ↔
      ¬ T.D2PowerSavingEstimate P data := by
  constructor
  · intro hfail hD2
    have hcommon : T.D2CommonScalarPowerSavingEstimate P data :=
      T.d2CommonScalarPowerSavingEstimate_of_d2PowerSavingEstimate P data hD2
    exact ((T.d2CommonScalarPowerSavingFailure_iff_not_d2CommonScalarPowerSavingEstimate P data).1
       hfail) hcommon
  · intro hnot
    exact (T.d2CommonScalarPowerSavingFailure_iff_not_d2CommonScalarPowerSavingEstimate P data).2
      (fun hcommon => hnot
        (T.d2PowerSavingEstimate_of_d2CommonScalarPowerSavingEstimate P data hcommon))

/-- Failure of E2 coverage is exactly simultaneous D1 and D2 universal failure. -/
theorem not_e2CommonScalarCoverage_iff_d1Failure_and_d2Failure
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    ¬ T.E2CommonScalarCoverage P data ↔
      T.D1CommonScalarPowerSavingFailure P data ∧
        T.D2CommonScalarPowerSavingFailure P data := by
  constructor
  · intro hnot
    constructor
    · exact (T.d1CommonScalarPowerSavingFailure_iff_not_d1CommonScalarPowerSavingEstimate P data).2
        (fun hD1 => hnot (Or.inl hD1))
    · exact (T.d2CommonScalarPowerSavingFailure_iff_not_d2CommonScalarPowerSavingEstimate P data).2
        (fun hD2 => hnot (Or.inr hD2))
  · intro hboth hcov
    rcases hcov with hD1 | hD2
    · exact ((T.d1CommonScalarPowerSavingFailure_iff_not_d1CommonScalarPowerSavingEstimate P data).1
         hboth.1) hD1
    · exact ((T.d2CommonScalarPowerSavingFailure_iff_not_d2CommonScalarPowerSavingEstimate P data).1
         hboth.2) hD2

end ABCTriple
end ABD2
