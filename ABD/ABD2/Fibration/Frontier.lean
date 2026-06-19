import ABD.ABD2.Fibration.LiftCost
import ABD.ABD2.Gauge.SmallSection
import ABD.ABD2.Gauge.PowerSaving

namespace ABD2
namespace ABCTriple

/-- Phase 9 base frontier: the qualitative obstruction before any lift-cost
estimate is attempted.

This is a fibration-language alias for `BaseObstruction`, hence for `BadSeed`:
all compatible AB-base points lie in the Wronskian-degenerate locus. -/
def BadSeedFrontier (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  T.BaseObstruction P

@[simp]
theorem badSeedFrontier_iff_baseObstruction
    (T : ABCTriple) (P : T.CImageProfile) :
    T.BadSeedFrontier P ↔ T.BaseObstruction P := by
  rfl

/-- The base frontier is the original `BadSeed` predicate. -/
theorem badSeedFrontier_iff_badSeed
    (T : ABCTriple) (P : T.CImageProfile) :
    T.BadSeedFrontier P ↔ T.BadSeed P := by
  exact (T.badSeedFrontier_iff_baseObstruction P).trans
    (T.baseObstruction_iff_badSeed P)

/-- Avoiding the base frontier is exactly the existence of a good base point. -/
theorem not_badSeedFrontier_iff_hasGoodBasePoint
    (T : ABCTriple) (P : T.CImageProfile) :
    ¬ T.BadSeedFrontier P ↔ T.HasGoodBasePoint P := by
  exact (not_congr (T.badSeedFrontier_iff_baseObstruction P)).trans
    (T.not_baseObstruction_iff_hasGoodBasePoint P)

/-- Fixed-bound lift failure after the base obstruction has been removed.

`SmallLiftFailureAt P B` says that there is a good base point, but no good base
point has C-lift cost at most the chosen bound `B`.  This isolates the
fixed-bound part of the problem from the base obstruction. -/
def SmallLiftFailureAt
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) : Prop :=
  T.HasGoodBasePoint P ∧ ¬ T.ProfileLiftCostAtMost P B

/-- Fixed-bound lift failure is the same statement with `SmallSectionExists` in
place of the cost vocabulary. -/
theorem smallLiftFailureAt_iff_hasGoodBasePoint_and_not_smallSectionExists
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) :
    T.SmallLiftFailureAt P B ↔
      T.HasGoodBasePoint P ∧ ¬ T.SmallSectionExists P B := by
  constructor
  · intro h
    exact ⟨h.1, fun hsection =>
      h.2 ((T.profileLiftCostAtMost_iff_smallSectionExists P B).2 hsection)⟩
  · intro h
    exact ⟨h.1, fun hcost =>
      h.2 ((T.profileLiftCostAtMost_iff_smallSectionExists P B).1 hcost)⟩

/-- A fixed-bound cost solution rules out fixed-bound lift failure. -/
theorem not_smallLiftFailureAt_of_profileLiftCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.ProfileLiftCostAtMost P B) :
    ¬ T.SmallLiftFailureAt P B := by
  intro hfail
  exact hfail.2 h

/-- Negating fixed-bound lift failure means: once a good base point exists, the
chosen bound actually works. -/
theorem not_smallLiftFailureAt_iff_hasGoodBasePoint_imp_profileLiftCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) :
    ¬ T.SmallLiftFailureAt P B ↔
      (T.HasGoodBasePoint P → T.ProfileLiftCostAtMost P B) := by
  constructor
  · intro hnot hbase
    by_contra hcost
    exact hnot ⟨hbase, hcost⟩
  · intro h hfail
    exact hfail.2 (h hfail.1)

/-- The fixed-bound frontier consists of the base obstruction or a remaining
fixed-bound lift failure. -/
def FixedBoundFrontier
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) : Prop :=
  T.BadSeedFrontier P ∨ T.SmallLiftFailureAt P B

/-- If neither fixed-bound frontier remains, then the profile has lift cost at
most `B`. -/
theorem profileLiftCostAtMost_of_not_fixedBoundFrontier
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : ¬ T.FixedBoundFrontier P B) :
    T.ProfileLiftCostAtMost P B := by
  have hnotBase : ¬ T.BadSeedFrontier P := by
    intro hbaseFrontier
    exact h (Or.inl hbaseFrontier)
  have hbase : T.HasGoodBasePoint P :=
    (T.not_badSeedFrontier_iff_hasGoodBasePoint P).1 hnotBase
  have hnotLift : ¬ T.SmallLiftFailureAt P B := by
    intro hfail
    exact h (Or.inr hfail)
  exact (T.not_smallLiftFailureAt_iff_hasGoodBasePoint_imp_profileLiftCostAtMost
    P B).1 hnotLift hbase

/-- If neither fixed-bound frontier remains, then there is a small strict
candidate at the same coordinate bound. -/
theorem hasSmallStrictCandidate_of_not_fixedBoundFrontier
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : ¬ T.FixedBoundFrontier P B) :
    ∃ x : T.FullTangent, T.StrictCandidate x ∧ T.SmallTangent x B := by
  exact T.hasSmallStrictCandidate_of_profileLiftCostAtMost P
    (T.profileLiftCostAtMost_of_not_fixedBoundFrontier P h)

/-- Finite lift failure after qualitative fibration is solved.

Phase 7 proves that this frontier is empty for the coordinate gauge: finite
boundedness is automatic once the qualitative fibration is solved. -/
def FiniteSmallLiftFailure
    (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  T.QualitativeFibrationSolved P ∧ ¬ T.HasFiniteProfileLiftCost P

/-- Finite coordinate-lift failure cannot occur after qualitative fibration is
solved.  The remaining hard problem is the quality of the bound, not mere finite
existence. -/
theorem not_finiteSmallLiftFailure
    (T : ABCTriple) (P : T.CImageProfile) :
    ¬ T.FiniteSmallLiftFailure P := by
  intro h
  exact h.2 (T.hasFiniteProfileLiftCost_of_qualitativeFibrationSolved P h.1)

/-- A gauge-small section whose bound is accepted by a bound regime. -/
def GaugeSmallSectionInRegime
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile)
    (R : T.BoundRegime) : Prop :=
  ∃ B : ℤ, R.accepts B ∧ T.GaugeSmallSectionExists G P B

/-- A regime-level gauge-small section is, in particular, a finite gauge-small
section. -/
theorem hasFiniteGaugeSmallSection_of_gaugeSmallSectionInRegime
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile)
    (R : T.BoundRegime)
    (h : T.GaugeSmallSectionInRegime G P R) :
    T.HasFiniteGaugeSmallSection G P := by
  rcases h with ⟨B, _hB, hsection⟩
  exact ⟨B, hsection⟩

/-- A regime-level gauge-small section routes to a power-saving candidate in the
abstract regime sense. -/
theorem hasPowerSavingCandidate_of_gaugeSmallSectionInRegime
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile)
    (R : T.PowerSavingRegime)
    (h : T.GaugeSmallSectionInRegime G P R) :
    T.HasPowerSavingCandidate G R := by
  rcases h with ⟨B, hB, hsection⟩
  exact T.hasGaugeCandidateInRegime_of_bound G R hB
    (T.hasSmallStrictCandidateWith_of_gaugeSmallSectionExists G P hsection)

/-- Regime-level lift failure after the base obstruction has been removed.

This is the proper abc-hard frontier: there is a good base point, but no section
with a bound accepted by the chosen power-saving regime. -/
def RegimeSmallLiftFailure
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile)
    (R : T.BoundRegime) : Prop :=
  T.HasGoodBasePoint P ∧ ¬ T.GaugeSmallSectionInRegime G P R

/-- Negating regime-level lift failure means: once a good base point exists, a
regime-accepted gauge-small section exists. -/
theorem not_regimeSmallLiftFailure_iff_hasGoodBasePoint_imp_gaugeSmallSectionInRegime
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile)
    (R : T.BoundRegime) :
    ¬ T.RegimeSmallLiftFailure G P R ↔
      (T.HasGoodBasePoint P → T.GaugeSmallSectionInRegime G P R) := by
  constructor
  · intro hnot hbase
    by_contra hregime
    exact hnot ⟨hbase, hregime⟩
  · intro h hfail
    exact hfail.2 (h hfail.1)

/-- Gauge hardness inside a regime: finite gauge-small sections exist, but none
with a regime-accepted bound. -/
def GaugeHardnessInRegime
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile)
    (R : T.BoundRegime) : Prop :=
  T.HasFiniteGaugeSmallSection G P ∧ ¬ T.GaugeSmallSectionInRegime G P R

/-- Regime-level lift failure plus a finite gauge-small section gives gauge
hardness in the chosen regime. -/
theorem gaugeHardnessInRegime_of_regimeSmallLiftFailure
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile)
    (R : T.BoundRegime)
    (hfinite : T.HasFiniteGaugeSmallSection G P)
    (hfail : T.RegimeSmallLiftFailure G P R) :
    T.GaugeHardnessInRegime G P R := by
  exact ⟨hfinite, hfail.2⟩

/-- Coordinate-gauge regime sections are exactly coordinate-small sections with an
accepted bound. -/
theorem gaugeSmallSectionInRegime_coordinateGauge_iff_exists_smallSectionExists
    (T : ABCTriple) (P : T.CImageProfile) (R : T.BoundRegime) :
    T.GaugeSmallSectionInRegime T.coordinateGauge P R ↔
      ∃ B : ℤ, R.accepts B ∧ T.SmallSectionExists P B := by
  constructor
  · intro h
    rcases h with ⟨B, hB, hsection⟩
    exact ⟨B, hB,
      (T.gaugeSmallSectionExists_coordinateGauge_iff_smallSectionExists P B).1 hsection⟩
  · intro h
    rcases h with ⟨B, hB, hsection⟩
    exact ⟨B, hB,
      (T.gaugeSmallSectionExists_coordinateGauge_iff_smallSectionExists P B).2 hsection⟩

/-- The abc-hard frontier for a fixed gauge and bound regime: either the base is
bad, or the base is good but no regime-accepted gauge-small section exists. -/
def ABCHardFrontier
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile)
    (R : T.PowerSavingRegime) : Prop :=
  T.BadSeedFrontier P ∨ T.RegimeSmallLiftFailure G P R

/-- If the abc-hard frontier is absent, a regime-level gauge-small section exists. -/
theorem gaugeSmallSectionInRegime_of_not_abcHardFrontier
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile)
    (R : T.PowerSavingRegime)
    (h : ¬ T.ABCHardFrontier G P R) :
    T.GaugeSmallSectionInRegime G P R := by
  have hnotBase : ¬ T.BadSeedFrontier P := by
    intro hbaseFrontier
    exact h (Or.inl hbaseFrontier)
  have hbase : T.HasGoodBasePoint P :=
    (T.not_badSeedFrontier_iff_hasGoodBasePoint P).1 hnotBase
  have hnotLift : ¬ T.RegimeSmallLiftFailure G P R := by
    intro hfail
    exact h (Or.inr hfail)
  exact (T.not_regimeSmallLiftFailure_iff_hasGoodBasePoint_imp_gaugeSmallSectionInRegime
    G P R).1 hnotLift hbase

/-- If the abc-hard frontier is absent, a power-saving candidate exists in the
chosen abstract regime. -/
theorem hasPowerSavingCandidate_of_not_abcHardFrontier
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile)
    (R : T.PowerSavingRegime)
    (h : ¬ T.ABCHardFrontier G P R) :
    T.HasPowerSavingCandidate G R := by
  exact T.hasPowerSavingCandidate_of_gaugeSmallSectionInRegime G P R
    (T.gaugeSmallSectionInRegime_of_not_abcHardFrontier G P R h)

end ABCTriple
end ABD2
