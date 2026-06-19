import ABD.ABD2.Regime.E2.FailureNormalForm

namespace ABD2
namespace ABCTriple

/-- E2 hard frontier.

This is the exact residual left after the common scalar route fails: D1 fails in
universal common-scalar normal form and D2 fails in universal common-scalar
normal form.  The point of naming this frontier is that later arithmetic files
can try to prove it forces a harmless radical/support pattern or an allowed
exceptional pattern. -/
def E2HardFrontier
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.D1CommonScalarPowerSavingFailure P data ∧
    T.D2CommonScalarPowerSavingFailure P data

/-- The hard frontier is just simultaneous D1/D2 E2 failure. -/
theorem e2HardFrontier_iff_d1Failure_and_d2Failure
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2HardFrontier P data ↔
      T.D1CommonScalarPowerSavingFailure P data ∧
        T.D2CommonScalarPowerSavingFailure P data := by
  rfl

/-- The hard frontier is exactly failure of E2 common scalar coverage. -/
theorem e2HardFrontier_iff_not_e2CommonScalarCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2HardFrontier P data ↔
      ¬ T.E2CommonScalarCoverage P data := by
  exact Iff.symm (T.not_e2CommonScalarCoverage_iff_d1Failure_and_d2Failure P data)

/-- Build the hard frontier from failure of E2 common scalar coverage. -/
theorem e2HardFrontier_of_not_e2CommonScalarCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : ¬ T.E2CommonScalarCoverage P data) :
    T.E2HardFrontier P data := by
  exact (T.e2HardFrontier_iff_not_e2CommonScalarCoverage P data).2 h

/-- The hard frontier implies failure of E2 common scalar coverage. -/
theorem not_e2CommonScalarCoverage_of_e2HardFrontier
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2HardFrontier P data) :
    ¬ T.E2CommonScalarCoverage P data := by
  exact (T.e2HardFrontier_iff_not_e2CommonScalarCoverage P data).1 h

/-- The hard frontier is also exactly the older E2 complement predicate. -/
theorem e2HardFrontier_iff_e2CommonScalarFailure
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2HardFrontier P data ↔
      T.E2CommonScalarFailure P data := by
  exact T.e2HardFrontier_iff_not_e2CommonScalarCoverage P data

/-- Convert the older E2 complement predicate into the hard frontier. -/
theorem e2HardFrontier_of_e2CommonScalarFailure
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2CommonScalarFailure P data) :
    T.E2HardFrontier P data := by
  exact (T.e2HardFrontier_iff_e2CommonScalarFailure P data).2 h

/-- The hard frontier implies the older E2 complement predicate. -/
theorem e2CommonScalarFailure_of_e2HardFrontier
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2HardFrontier P data) :
    T.E2CommonScalarFailure P data := by
  exact (T.e2HardFrontier_iff_e2CommonScalarFailure P data).1 h

/-- First projection from the hard frontier. -/
theorem d1Failure_of_e2HardFrontier
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2HardFrontier P data) :
    T.D1CommonScalarPowerSavingFailure P data := by
  exact h.1

/-- Second projection from the hard frontier. -/
theorem d2Failure_of_e2HardFrontier
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2HardFrontier P data) :
    T.D2CommonScalarPowerSavingFailure P data := by
  exact h.2

/-- Existing E branch-coverage failure is equivalent to the E2 hard frontier. -/
theorem e2HardFrontier_iff_not_branchPowerSavingCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2HardFrontier P data ↔
      ¬ T.BranchPowerSavingCoverage P data := by
  constructor
  · intro hfront hbranch
    have hcov : T.E2CommonScalarCoverage P data :=
      T.e2CommonScalarCoverage_of_branchPowerSavingCoverage P data hbranch
    exact (T.not_e2CommonScalarCoverage_of_e2HardFrontier P data hfront) hcov
  · intro hnotBranch
    apply T.e2HardFrontier_of_not_e2CommonScalarCoverage P data
    intro hcov
    exact hnotBranch (T.branchPowerSavingCoverage_of_e2CommonScalarCoverage P data hcov)

end ABCTriple
end ABD2
