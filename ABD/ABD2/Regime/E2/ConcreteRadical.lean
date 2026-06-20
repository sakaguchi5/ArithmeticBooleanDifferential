import ABD.ABD2.Regime.E2.RadicalReductionGoal

namespace ABD2
namespace ABCTriple

/-- Squarefree radical attached to the ABD2 support.

At this layer we deliberately use the already-chosen full support of the triple:
`support = supportA ∪ supportB ∪ supportC`.  Since each block is a prime support,
the product of the support primes is the natural squarefree radical candidate for
`abc` in the E2 contrapositive route. -/
def RadABC (T : ABCTriple) : ℕ :=
  T.support.prod (fun p => p)

/-- Concrete large-radical condition for the E2 route.

This is the integer-power version of the informal comparison
`c^(M/N) ≤ rad(abc)`.  It is aligned with the existing rational power-saving
inequality `B^N < c^M`: if the common-scalar routes fail but this condition holds,
then the triple is intended to be harmless from the radical side. -/
def E2RadicalLarge
    (T : ABCTriple) (data : RationalPowerSavingData) : Prop :=
  ((T.c : ℤ) ^ data.M) ≤ ((T.RadABC : ℤ) ^ data.N)

/-- First concrete exceptional pattern for the E2 route.

This is intentionally conservative: it records the obvious one-sided unit
boundary that should later be compared with the precise Pasten/SDC exceptional
family.  Later files may strengthen this by adding support-singleton or
prime-power-like conditions on the `c` side. -/
def E2PastenExceptionalPattern (T : ABCTriple) : Prop :=
  T.a = 1 ∨ T.b = 1

/-- Concrete E2 radical-reduction goal.

The abstract `E2RadicalReductionGoal` is instantiated with the concrete radical
condition `E2RadicalLarge` and the first-pass Pasten exceptional predicate
`E2PastenExceptionalPattern`.  This is the next general-proof target:
if both common-scalar routes fail, then either the radical is already large or
the triple lies in the permitted exceptional boundary. -/
def E2ConcreteRadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.E2RadicalReductionGoal P data
    (T.E2RadicalLarge data)
    T.E2PastenExceptionalPattern

/-- Unfold the concrete radical-reduction goal into its working implication. -/
theorem e2ConcreteRadicalReductionGoal_iff
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2ConcreteRadicalReductionGoal P data ↔
      (T.E2HardFrontier P data →
        T.E2RadicalLarge data ∨ T.E2PastenExceptionalPattern) := by
  rfl

/-- Use the concrete radical-reduction goal on a hard-frontier witness. -/
theorem e2RadicalOrExceptional_of_e2ConcreteRadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.E2ConcreteRadicalReductionGoal P data)
    (hfront : T.E2HardFrontier P data) :
    T.E2RadicalLarge data ∨ T.E2PastenExceptionalPattern := by
  exact hgoal hfront

/-- The concrete radical-reduction goal gives the final E2 logical split. -/
theorem e2GeneralReductionConclusion_of_e2ConcreteRadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.E2ConcreteRadicalReductionGoal P data) :
    T.E2GeneralReductionConclusion P data
      (T.E2RadicalLarge data)
      T.E2PastenExceptionalPattern := by
  exact T.e2GeneralReductionConclusion_of_e2RadicalReductionGoal P data
    (T.E2RadicalLarge data)
    T.E2PastenExceptionalPattern
    hgoal

/-- E2 coverage alone gives the concrete final split. -/
theorem e2ConcreteGeneralReductionConclusion_of_coverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hcov : T.E2CommonScalarCoverage P data) :
    T.E2GeneralReductionConclusion P data
      (T.E2RadicalLarge data)
      T.E2PastenExceptionalPattern := by
  exact T.e2GeneralReductionConclusion_of_e2CommonScalarCoverage P data
    (T.E2RadicalLarge data)
    T.E2PastenExceptionalPattern
    hcov

/-- A concrete radical-large witness gives the concrete final split. -/
theorem e2ConcreteGeneralReductionConclusion_of_radicalLarge
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hlarge : T.E2RadicalLarge data) :
    T.E2GeneralReductionConclusion P data
      (T.E2RadicalLarge data)
      T.E2PastenExceptionalPattern := by
  exact T.e2GeneralReductionConclusion_of_radicalOrExceptional P data
    (T.E2RadicalLarge data)
    T.E2PastenExceptionalPattern
    (Or.inl hlarge)

/-- A concrete exceptional-pattern witness gives the concrete final split. -/
theorem e2ConcreteGeneralReductionConclusion_of_exceptional
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hexceptional : T.E2PastenExceptionalPattern) :
    T.E2GeneralReductionConclusion P data
      (T.E2RadicalLarge data)
      T.E2PastenExceptionalPattern := by
  exact T.e2GeneralReductionConclusion_of_radicalOrExceptional P data
    (T.E2RadicalLarge data)
    T.E2PastenExceptionalPattern
    (Or.inr hexceptional)

end ABCTriple
end ABD2
