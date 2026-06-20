import ABD.ABD2.Regime.E2.ConcreteDanger

namespace ABD2
namespace ABCTriple

/-- Concrete radical-small inequality for the E2 dangerous zone.

This is the strict opposite of `E2RadicalLarge` written as an explicit
integer-power inequality:

`rad(abc)^N < c^M`.

It is the arithmetic form of "the radical route is not already harmless" for
the chosen rational power-saving data. -/
def E2RadicalSmallInequality
    (T : ABCTriple) (data : RationalPowerSavingData) : Prop :=
  ((T.RadABC : ℤ) ^ data.N) < ((T.c : ℤ) ^ data.M)

/-- The radical-small inequality is equivalent to the negation of the concrete
large-radical condition. -/
theorem e2RadicalSmallInequality_iff_not_radicalLarge
    (T : ABCTriple) (data : RationalPowerSavingData) :
    T.E2RadicalSmallInequality data ↔ ¬ T.E2RadicalLarge data := by
  unfold E2RadicalSmallInequality E2RadicalLarge
  constructor
  · intro hsmall
    exact (not_le).2 hsmall
  · intro hnotLarge
    exact (not_le).1 hnotLarge

/-- A non-exceptional triple for the first-pass E2 exceptional boundary.

Since the current concrete exceptional predicate is `a = 1 ∨ b = 1`, the
corresponding non-exceptional condition is `a ≠ 1 ∧ b ≠ 1`. -/
def E2NonExceptionalPattern (T : ABCTriple) : Prop :=
  T.a ≠ 1 ∧ T.b ≠ 1

/-- The non-exceptional predicate is equivalent to negating the current concrete
Pasten exceptional boundary. -/
theorem e2NonExceptionalPattern_iff_not_exceptional
    (T : ABCTriple) :
    T.E2NonExceptionalPattern ↔ ¬ T.E2PastenExceptionalPattern := by
  unfold E2NonExceptionalPattern E2PastenExceptionalPattern
  constructor
  · intro hnon hexceptional
    rcases hexceptional with ha | hb
    · exact hnon.1 ha
    · exact hnon.2 hb
  · intro hnot
    constructor
    · intro ha
      exact hnot (Or.inl ha)
    · intro hb
      exact hnot (Or.inr hb)

/-- Fully concrete normal form of the E2 dangerous zone.

A triple is dangerous exactly when the radical is genuinely small in the
integer-power sense and the triple is not in the current exceptional boundary. -/
def E2ConcreteDangerNormalForm
    (T : ABCTriple) (data : RationalPowerSavingData) : Prop :=
  T.E2RadicalSmallInequality data ∧ T.E2NonExceptionalPattern

/-- The existing dangerous predicate is equivalent to its concrete normal form. -/
theorem e2Dangerous_iff_concreteDangerNormalForm
    (T : ABCTriple) (data : RationalPowerSavingData) :
    T.E2Dangerous data ↔ T.E2ConcreteDangerNormalForm data := by
  constructor
  · intro hdanger
    rcases hdanger with ⟨hnotLarge, hnotExceptional⟩
    exact ⟨
      (T.e2RadicalSmallInequality_iff_not_radicalLarge data).2 hnotLarge,
      (T.e2NonExceptionalPattern_iff_not_exceptional).2 hnotExceptional⟩
  · intro hnormal
    rcases hnormal with ⟨hsmall, hnon⟩
    exact ⟨
      (T.e2RadicalSmallInequality_iff_not_radicalLarge data).1 hsmall,
      (T.e2NonExceptionalPattern_iff_not_exceptional).1 hnon⟩

/-- A dangerous triple has radical-small inequality. -/
theorem e2RadicalSmallInequality_of_e2Dangerous
    (T : ABCTriple) (data : RationalPowerSavingData)
    (h : T.E2Dangerous data) :
    T.E2RadicalSmallInequality data := by
  exact (T.e2Dangerous_iff_concreteDangerNormalForm data).1 h |>.1

/-- A dangerous triple is non-exceptional. -/
theorem e2NonExceptionalPattern_of_e2Dangerous
    (T : ABCTriple) (data : RationalPowerSavingData)
    (h : T.E2Dangerous data) :
    T.E2NonExceptionalPattern := by
  exact (T.e2Dangerous_iff_concreteDangerNormalForm data).1 h |>.2

/-- In the E2 dangerous zone, `a` is not the unit boundary. -/
theorem a_ne_one_of_e2Dangerous
    (T : ABCTriple) (data : RationalPowerSavingData)
    (h : T.E2Dangerous data) :
    T.a ≠ 1 := by
  exact (T.e2NonExceptionalPattern_of_e2Dangerous data h).1

/-- In the E2 dangerous zone, `b` is not the unit boundary. -/
theorem b_ne_one_of_e2Dangerous
    (T : ABCTriple) (data : RationalPowerSavingData)
    (h : T.E2Dangerous data) :
    T.b ≠ 1 := by
  exact (T.e2NonExceptionalPattern_of_e2Dangerous data h).2

/-- Coverage goal stated over the fully concrete dangerous normal form. -/
def E2ConcreteDangerCoverageGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.E2ConcreteDangerNormalForm data → T.E2CommonScalarCoverage P data

/-- Concrete-normal-form coverage is equivalent to the existing dangerous-zone
coverage goal. -/
theorem e2ConcreteDangerCoverageGoal_iff_e2DangerousCoverageGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2ConcreteDangerCoverageGoal P data ↔
      T.E2DangerousCoverageGoal P data := by
  constructor
  · intro hgoal hdanger
    exact hgoal ((T.e2Dangerous_iff_concreteDangerNormalForm data).1 hdanger)
  · intro hgoal hnormal
    exact hgoal ((T.e2Dangerous_iff_concreteDangerNormalForm data).2 hnormal)

/-- The concrete-normal-form coverage goal is equivalent to the concrete
radical-reduction goal. -/
theorem e2ConcreteDangerCoverageGoal_iff_e2ConcreteRadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2ConcreteDangerCoverageGoal P data ↔
      T.E2ConcreteRadicalReductionGoal P data := by
  constructor
  · intro hgoal
    exact T.e2ConcreteRadicalReductionGoal_of_e2DangerousCoverageGoal P data
      ((T.e2ConcreteDangerCoverageGoal_iff_e2DangerousCoverageGoal P data).1 hgoal)
  · intro hgoal hnormal
    have hdanger : T.E2Dangerous data :=
      (T.e2Dangerous_iff_concreteDangerNormalForm data).2 hnormal
    exact T.e2CommonScalarCoverage_of_e2ConcreteRadicalReductionGoal_of_e2Dangerous
      P data hgoal hdanger

/-- A concrete dangerous-normal-form witness gives E2 coverage once the concrete
radical-reduction goal has been supplied. -/
theorem e2CommonScalarCoverage_of_e2ConcreteRadicalReductionGoal_of_concreteDanger
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.E2ConcreteRadicalReductionGoal P data)
    (hnormal : T.E2ConcreteDangerNormalForm data) :
    T.E2CommonScalarCoverage P data := by
  exact ((T.e2ConcreteDangerCoverageGoal_iff_e2ConcreteRadicalReductionGoal P data).2
    hgoal) hnormal

end ABCTriple
end ABD2
