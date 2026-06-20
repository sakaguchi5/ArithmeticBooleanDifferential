import ABD.ABD2.Regime.E2.ConcreteRadical

namespace ABD2
namespace ABCTriple

/-- The concrete dangerous zone for the E2 contrapositive route.

A triple is dangerous, relative to the chosen rational power-saving data, when it
is not already harmless by the concrete radical-large condition and it is not in
the current exceptional boundary.  This is the zone where the common-scalar
coverage must be proved directly. -/
def E2Dangerous
    (T : ABCTriple) (data : RationalPowerSavingData) : Prop :=
  ¬ T.E2RadicalLarge data ∧ ¬ T.E2PastenExceptionalPattern

/-- Unfold the concrete dangerous zone. -/
theorem e2Dangerous_iff_not_radicalLarge_and_not_exceptional
    (T : ABCTriple) (data : RationalPowerSavingData) :
    T.E2Dangerous data ↔
      ¬ T.E2RadicalLarge data ∧ ¬ T.E2PastenExceptionalPattern := by
  rfl

/-- A dangerous triple is exactly outside the concrete radical-or-exceptional
conclusion. -/
theorem not_e2RadicalOrExceptional_of_e2Dangerous
    (T : ABCTriple) (data : RationalPowerSavingData)
    (h : T.E2Dangerous data) :
    ¬ T.E2RadicalOrExceptional
      (T.E2RadicalLarge data)
      T.E2PastenExceptionalPattern := by
  intro hro
  rcases h with ⟨hnotLarge, hnotExceptional⟩
  rcases hro with hlarge | hexceptional
  · exact hnotLarge hlarge
  · exact hnotExceptional hexceptional

/-- Being outside the concrete radical-or-exceptional conclusion gives the
concrete dangerous zone. -/
theorem e2Dangerous_of_not_e2RadicalOrExceptional
    (T : ABCTriple) (data : RationalPowerSavingData)
    (h : ¬ T.E2RadicalOrExceptional
      (T.E2RadicalLarge data)
      T.E2PastenExceptionalPattern) :
    T.E2Dangerous data := by
  constructor
  · intro hlarge
    exact h (Or.inl hlarge)
  · intro hexceptional
    exact h (Or.inr hexceptional)

/-- The concrete dangerous zone is equivalent to negating the concrete
radical-or-exceptional conclusion. -/
theorem e2Dangerous_iff_not_e2RadicalOrExceptional
    (T : ABCTriple) (data : RationalPowerSavingData) :
    T.E2Dangerous data ↔
      ¬ T.E2RadicalOrExceptional
        (T.E2RadicalLarge data)
        T.E2PastenExceptionalPattern := by
  constructor
  · exact T.not_e2RadicalOrExceptional_of_e2Dangerous data
  · exact T.e2Dangerous_of_not_e2RadicalOrExceptional data

/-- The concrete radical-or-exceptional conclusion excludes the dangerous zone. -/
theorem not_e2Dangerous_of_e2RadicalOrExceptional
    (T : ABCTriple) (data : RationalPowerSavingData)
    (h : T.E2RadicalOrExceptional
      (T.E2RadicalLarge data)
      T.E2PastenExceptionalPattern) :
    ¬ T.E2Dangerous data := by
  intro hdanger
  exact (T.not_e2RadicalOrExceptional_of_e2Dangerous data hdanger) h

/-- Dangerous-coverage form of the E2 concrete reduction.

This is the contrapositive form that is useful for the general proof: instead of
proving coverage for all triples, it suffices to prove coverage only for triples
that are not already radical-large and not exceptional. -/
def E2DangerousCoverageGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.E2Dangerous data → T.E2CommonScalarCoverage P data

/-- The concrete radical-reduction goal is equivalent to proving E2 coverage on
only the concrete dangerous zone. -/
theorem e2DangerousCoverageGoal_iff_e2ConcreteRadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2DangerousCoverageGoal P data ↔
      T.E2ConcreteRadicalReductionGoal P data := by
  constructor
  · intro hgoal hfront
    classical
    by_cases hlarge : T.E2RadicalLarge data
    · exact Or.inl hlarge
    · by_cases hexceptional : T.E2PastenExceptionalPattern
      · exact Or.inr hexceptional
      · have hdanger : T.E2Dangerous data := ⟨hlarge, hexceptional⟩
        have hcov : T.E2CommonScalarCoverage P data := hgoal hdanger
        have hnotCov : ¬ T.E2CommonScalarCoverage P data :=
          T.not_e2CommonScalarCoverage_of_e2HardFrontier P data hfront
        exact False.elim (hnotCov hcov)
  · intro hgoal hdanger
    classical
    by_cases hcov : T.E2CommonScalarCoverage P data
    · exact hcov
    · have hfront : T.E2HardFrontier P data :=
        T.e2HardFrontier_of_not_e2CommonScalarCoverage P data hcov
      have hro : T.E2RadicalOrExceptional
          (T.E2RadicalLarge data)
          T.E2PastenExceptionalPattern := hgoal hfront
      have hnotRO : ¬ T.E2RadicalOrExceptional
          (T.E2RadicalLarge data)
          T.E2PastenExceptionalPattern :=
        T.not_e2RadicalOrExceptional_of_e2Dangerous data hdanger
      exact False.elim (hnotRO hro)

/-- Convert dangerous-zone coverage into the concrete radical-reduction goal. -/
theorem e2ConcreteRadicalReductionGoal_of_e2DangerousCoverageGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2DangerousCoverageGoal P data) :
    T.E2ConcreteRadicalReductionGoal P data := by
  exact (T.e2DangerousCoverageGoal_iff_e2ConcreteRadicalReductionGoal P data).1 h

/-- Convert the concrete radical-reduction goal into dangerous-zone coverage. -/
theorem e2DangerousCoverageGoal_of_e2ConcreteRadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2ConcreteRadicalReductionGoal P data) :
    T.E2DangerousCoverageGoal P data := by
  exact (T.e2DangerousCoverageGoal_iff_e2ConcreteRadicalReductionGoal P data).2 h

/-- If the concrete radical-reduction goal holds, then every dangerous triple has
E2 common-scalar coverage. -/
theorem e2CommonScalarCoverage_of_e2ConcreteRadicalReductionGoal_of_e2Dangerous
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.E2ConcreteRadicalReductionGoal P data)
    (hdanger : T.E2Dangerous data) :
    T.E2CommonScalarCoverage P data := by
  exact (T.e2DangerousCoverageGoal_of_e2ConcreteRadicalReductionGoal P data hgoal)
    hdanger

/-- The concrete radical-reduction goal gives the final dichotomy: either E2
coverage already holds, or the triple is not in the dangerous zone. -/
theorem e2Coverage_or_not_dangerous_of_e2ConcreteRadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.E2ConcreteRadicalReductionGoal P data) :
    T.E2CommonScalarCoverage P data ∨ ¬ T.E2Dangerous data := by
  classical
  by_cases hcov : T.E2CommonScalarCoverage P data
  · exact Or.inl hcov
  · have hfront : T.E2HardFrontier P data :=
      T.e2HardFrontier_of_not_e2CommonScalarCoverage P data hcov
    have hro : T.E2RadicalOrExceptional
        (T.E2RadicalLarge data)
        T.E2PastenExceptionalPattern := hgoal hfront
    exact Or.inr (T.not_e2Dangerous_of_e2RadicalOrExceptional data hro)

/-- Coverage on the dangerous zone is enough to get the final dichotomy. -/
theorem e2Coverage_or_not_dangerous_of_e2DangerousCoverageGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.E2DangerousCoverageGoal P data) :
    T.E2CommonScalarCoverage P data ∨ ¬ T.E2Dangerous data := by
  exact T.e2Coverage_or_not_dangerous_of_e2ConcreteRadicalReductionGoal P data
    (T.e2ConcreteRadicalReductionGoal_of_e2DangerousCoverageGoal P data hgoal)

end ABCTriple
end ABD2
