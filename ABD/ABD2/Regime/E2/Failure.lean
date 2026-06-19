import ABD.ABD2.Regime.E2.Coverage

namespace ABD2
namespace ABCTriple

/-- E2 failure: neither common scalar reformulation succeeds.

This is intentionally defined as the complement of E2 coverage.  It is the
right object for the contrapositive route: instead of constructing D1/D2
directly, prove that this failure implies a harmless radical/support pattern or
an allowed exceptional pattern.
-/
def E2CommonScalarFailure
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  ¬ T.E2CommonScalarCoverage P data

/-- E2 failure is equivalent to failure of the existing E branch coverage. -/
theorem e2CommonScalarFailure_iff_not_branchPowerSavingCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2CommonScalarFailure P data ↔
      ¬ T.BranchPowerSavingCoverage P data := by
  constructor
  · intro h hb
    exact h (T.e2CommonScalarCoverage_of_branchPowerSavingCoverage P data hb)
  · intro h hc
    exact h (T.branchPowerSavingCoverage_of_e2CommonScalarCoverage P data hc)

/-- Existing E branch-coverage failure can be viewed as E2 common-scalar failure. -/
theorem e2CommonScalarFailure_of_not_branchPowerSavingCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : ¬ T.BranchPowerSavingCoverage P data) :
    T.E2CommonScalarFailure P data := by
  exact (T.e2CommonScalarFailure_iff_not_branchPowerSavingCoverage P data).2 h

/-- E2 common-scalar failure implies failure of existing E branch coverage. -/
theorem not_branchPowerSavingCoverage_of_e2CommonScalarFailure
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2CommonScalarFailure P data) :
    ¬ T.BranchPowerSavingCoverage P data := by
  exact (T.e2CommonScalarFailure_iff_not_branchPowerSavingCoverage P data).1 h

/-- Contrapositive target for the E2 route.

A future general proof can attack this statement: if common scalar coverage
fails, then the triple is harmless for an external reason.  The predicate
`Harmless` is deliberately abstract here so later files can instantiate it with
large radical, exceptional Pasten pattern, or any other final obstruction class.
-/
def E2FailureImplies
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (Harmless : Prop) : Prop :=
  T.E2CommonScalarFailure P data → Harmless

/-- If E2 coverage holds, the abstract failure implication is vacuous. -/
theorem e2FailureImplies_of_e2CommonScalarCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (Harmless : Prop)
    (hcov : T.E2CommonScalarCoverage P data) :
    T.E2FailureImplies P data Harmless := by
  intro hfail
  exact False.elim (hfail hcov)

end ABCTriple
end ABD2
