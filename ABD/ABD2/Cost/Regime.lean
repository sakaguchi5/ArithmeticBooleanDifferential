import ABD.ABD2.Cost.Gauge
import ABD.ABD2.Gauge.PowerSaving

namespace ABD2
namespace ABCTriple

/-- C1 in-regime predicate: the two-sided AB-cancellation cost has some accepted
bound.  This intentionally does not yet assert a full small candidate; it only
registers that the normalized two-sided AB cost lies in the chosen regime. -/
def TwoSidedABCancellationCostInRegime
    (T : ABCTriple) (R : T.BoundRegime) : Prop :=
  ∃ B : ℤ, R.accepts B ∧ T.TwoSidedABCancellationCostAtMost B

/-- C2a in-regime predicate for a fixed scalar target. -/
def PureForcedCLiftCostInRegime
    (T : ABCTriple) (G : T.Gauge) (R : T.BoundRegime) (t : ℤ) : Prop :=
  ∃ B : ℤ, R.accepts B ∧ T.GaugePureForcedCLiftCostAtMost G t B

/-- C2b in-regime predicate: one-sided forced cost has an accepted gauge bound. -/
def OneSidedForcedCostInRegime
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (R : T.BoundRegime) : Prop :=
  ∃ B : ℤ, R.accepts B ∧ T.GaugeOneSidedForcedCostAtMost P G B

/-- A concrete two-sided cost bound accepted by a regime gives C1 in-regime cost. -/
theorem twoSidedABCancellationCostInRegime_of_bound
    (T : ABCTriple) (R : T.BoundRegime) {B : ℤ}
    (hB : R.accepts B) (hcost : T.TwoSidedABCancellationCostAtMost B) :
    T.TwoSidedABCancellationCostInRegime R := by
  exact ⟨B, hB, hcost⟩

/-- A concrete gauge pure C-lift cost bound accepted by a regime gives C2a
in-regime cost. -/
theorem pureForcedCLiftCostInRegime_of_bound
    (T : ABCTriple) (G : T.Gauge) (R : T.BoundRegime) {t B : ℤ}
    (hB : R.accepts B) (hcost : T.GaugePureForcedCLiftCostAtMost G t B) :
    T.PureForcedCLiftCostInRegime G R t := by
  exact ⟨B, hB, hcost⟩

/-- A concrete gauge one-sided forced cost bound accepted by a regime gives C2b
in-regime cost. -/
theorem oneSidedForcedCostInRegime_of_bound
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.BoundRegime)
    {B : ℤ}
    (hB : R.accepts B) (hcost : T.GaugeOneSidedForcedCostAtMost P G B) :
    T.OneSidedForcedCostInRegime P G R := by
  exact ⟨B, hB, hcost⟩

/-- C2b in-regime cost produces a gauge candidate in the same regime. -/
theorem hasGaugeCandidateInRegime_of_oneSidedForcedCostInRegime
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.BoundRegime)
    (h : T.OneSidedForcedCostInRegime P G R) :
    T.HasGaugeCandidateInRegime G R := by
  rcases h with ⟨B, hB, hcost⟩
  exact T.hasGaugeCandidateInRegime_of_bound G R hB
    (T.hasSmallStrictCandidateWith_of_gaugeOneSidedForcedCostAtMost P G hcost)

/-- In a power-saving regime, C2b cost produces a power-saving candidate. -/
theorem hasPowerSavingCandidate_of_oneSidedForcedCostInRegime
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.PowerSavingRegime)
    (h : T.OneSidedForcedCostInRegime P G R) :
    T.HasPowerSavingCandidate G R := by
  exact T.hasGaugeCandidateInRegime_of_oneSidedForcedCostInRegime P G R h

/-- Coordinate C2b cost at an accepted bound produces a coordinate-gauge candidate
in the regime. -/
theorem hasGaugeCandidateInRegime_coordinateGauge_of_oneSidedForcedCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (R : T.BoundRegime) {B : ℤ}
    (hB : R.accepts B) (hcost : T.OneSidedForcedCostAtMost P B) :
    T.HasGaugeCandidateInRegime T.coordinateGauge R := by
  exact T.hasGaugeCandidateInRegime_of_bound T.coordinateGauge R hB
    (T.hasSmallStrictCandidateWith_coordinateGauge_of_oneSidedForcedCostAtMost P hcost)

end ABCTriple
end ABD2
