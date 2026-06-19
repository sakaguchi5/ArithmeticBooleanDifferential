import ABD.ABD2.Regime.E2.HardFrontier

namespace ABD2
namespace ABCTriple

/-- Abstract conclusion for the contrapositive route.

Later files should instantiate `RadicalLarge` with a concrete large-radical
condition and `ExceptionalPattern` with the permitted Pasten/SDC exceptional
shape.  For now this file only packages the logical reduction. -/
def E2RadicalOrExceptional
    (_T : ABCTriple) (RadicalLarge ExceptionalPattern : Prop) : Prop :=
  RadicalLarge ∨ ExceptionalPattern

/-- E2 radical reduction goal.

This is the next general-proof target: if both common-scalar routes fail, then
the triple must be harmless for an external reason, represented abstractly as
large radical or an allowed exceptional pattern. -/
def E2RadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (RadicalLarge ExceptionalPattern : Prop) : Prop :=
  T.E2HardFrontier P data →
    T.E2RadicalOrExceptional RadicalLarge ExceptionalPattern

/-- The radical-reduction goal is the same as the existing abstract failure
implication, once the harmless conclusion is taken to be radical-large or
exceptional. -/
theorem e2RadicalReductionGoal_iff_e2FailureImplies
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (RadicalLarge ExceptionalPattern : Prop) :
    T.E2RadicalReductionGoal P data RadicalLarge ExceptionalPattern ↔
      T.E2FailureImplies P data
        (T.E2RadicalOrExceptional RadicalLarge ExceptionalPattern) := by
  constructor
  · intro hgoal hfail
    exact hgoal (T.e2HardFrontier_of_e2CommonScalarFailure P data hfail)
  · intro himpl hfront
    exact himpl (T.e2CommonScalarFailure_of_e2HardFrontier P data hfront)

/-- Build the older abstract failure implication from the radical-reduction goal. -/
theorem e2FailureImplies_of_e2RadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (RadicalLarge ExceptionalPattern : Prop)
    (hgoal : T.E2RadicalReductionGoal P data RadicalLarge ExceptionalPattern) :
    T.E2FailureImplies P data
      (T.E2RadicalOrExceptional RadicalLarge ExceptionalPattern) := by
  exact (T.e2RadicalReductionGoal_iff_e2FailureImplies P data
    RadicalLarge ExceptionalPattern).1 hgoal

/-- Recover the radical-reduction goal from the older abstract failure implication. -/
theorem e2RadicalReductionGoal_of_e2FailureImplies
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (RadicalLarge ExceptionalPattern : Prop)
    (himpl : T.E2FailureImplies P data
      (T.E2RadicalOrExceptional RadicalLarge ExceptionalPattern)) :
    T.E2RadicalReductionGoal P data RadicalLarge ExceptionalPattern := by
  exact (T.e2RadicalReductionGoal_iff_e2FailureImplies P data
    RadicalLarge ExceptionalPattern).2 himpl

/-- Final logical split exposed by E2.

Either E2 common-scalar coverage succeeds, or the external harmless conclusion
must be supplied.  This is not yet the arithmetic theorem; it is the logical
shape that the general proof should aim to fill. -/
def E2GeneralReductionConclusion
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (RadicalLarge ExceptionalPattern : Prop) : Prop :=
  T.E2CommonScalarCoverage P data ∨
    T.E2RadicalOrExceptional RadicalLarge ExceptionalPattern

/-- If the radical-reduction goal is available, then every triple satisfies the
E2 logical split: either coverage holds, or the hard frontier forces the harmless
conclusion. -/
theorem e2GeneralReductionConclusion_of_e2RadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (RadicalLarge ExceptionalPattern : Prop)
    (hgoal : T.E2RadicalReductionGoal P data RadicalLarge ExceptionalPattern) :
    T.E2GeneralReductionConclusion P data RadicalLarge ExceptionalPattern := by
  classical
  by_cases hcov : T.E2CommonScalarCoverage P data
  · exact Or.inl hcov
  · exact Or.inr (hgoal (T.e2HardFrontier_of_not_e2CommonScalarCoverage P data hcov))

/-- E2 coverage alone gives the final logical split. -/
theorem e2GeneralReductionConclusion_of_e2CommonScalarCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (RadicalLarge ExceptionalPattern : Prop)
    (hcov : T.E2CommonScalarCoverage P data) :
    T.E2GeneralReductionConclusion P data RadicalLarge ExceptionalPattern := by
  exact Or.inl hcov

/-- A harmless conclusion alone gives the final logical split. -/
theorem e2GeneralReductionConclusion_of_radicalOrExceptional
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (RadicalLarge ExceptionalPattern : Prop)
    (h : T.E2RadicalOrExceptional RadicalLarge ExceptionalPattern) :
    T.E2GeneralReductionConclusion P data RadicalLarge ExceptionalPattern := by
  exact Or.inr h

end ABCTriple
end ABD2
