import ABD.ABD2.Regime.E2.Graph.GCDExpansion
import ABD.ABD2.Regime.E2.ConcreteRadical

namespace ABD2
namespace ABCTriple

/-- Step-5 target: graph desynchronization forces the harmless side of the E2
split.

This is intentionally a goal predicate, not asserted as a theorem.  It is the
formal landing zone for the future surplus-absorption argument:

`no accepted edge → C-surplus cannot be absorbed cheaply → radical large or
exceptional`. -/
def ScalarDesyncRadicalOrExceptionalGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.ScalarDesynchronization P data →
    T.E2RadicalLarge data ∨ T.E2PastenExceptionalPattern

/-- A stronger pure radical version of the surplus-absorption target. -/
def ScalarDesyncForcesRadicalLargeGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.ScalarDesynchronization P data → T.E2RadicalLarge data

/-- The pure radical version implies the radical-or-exceptional version. -/
theorem scalarDesyncRadicalOrExceptionalGoal_of_forcesRadicalLargeGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.ScalarDesyncForcesRadicalLargeGoal P data) :
    T.ScalarDesyncRadicalOrExceptionalGoal P data := by
  intro hdesync
  exact Or.inl (h hdesync)

/-- The graph desynchronization radical-or-exceptional goal is exactly the
concrete E2 radical-reduction goal, with the old hard frontier replaced by the
new graph frontier. -/
theorem scalarDesyncRadicalOrExceptionalGoal_iff_e2ConcreteRadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.ScalarDesyncRadicalOrExceptionalGoal P data ↔
      T.E2ConcreteRadicalReductionGoal P data := by
  constructor
  · intro hdesync hfront
    exact hdesync (T.scalarDesynchronization_of_e2HardFrontier P data hfront)
  · intro hgoal hdesync
    exact hgoal (T.e2HardFrontier_of_scalarDesynchronization P data hdesync)

/-- A graph desynchronization surplus-absorption goal supplies the existing
concrete radical-reduction goal. -/
theorem e2ConcreteRadicalReductionGoal_of_scalarDesyncRadicalOrExceptionalGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.ScalarDesyncRadicalOrExceptionalGoal P data) :
    T.E2ConcreteRadicalReductionGoal P data := by
  exact (T.scalarDesyncRadicalOrExceptionalGoal_iff_e2ConcreteRadicalReductionGoal P data).1 h

/-- The existing concrete radical-reduction goal can be read as the graph
surplus-absorption target. -/
theorem scalarDesyncRadicalOrExceptionalGoal_of_e2ConcreteRadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2ConcreteRadicalReductionGoal P data) :
    T.ScalarDesyncRadicalOrExceptionalGoal P data := by
  exact (T.scalarDesyncRadicalOrExceptionalGoal_iff_e2ConcreteRadicalReductionGoal P data).2 h

/-- Final graph-form split: either an accepted edge already exists, or the
surplus-absorption goal returns radical-large/exceptional. -/
theorem acceptedEdge_or_radicalOrExceptional_of_surplusAbsorptionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.ScalarDesyncRadicalOrExceptionalGoal P data) :
    T.HasAcceptedScalarSyncEdge P data ∨
      T.E2RadicalLarge data ∨ T.E2PastenExceptionalPattern := by
  by_cases hEdge : T.HasAcceptedScalarSyncEdge P data
  · exact Or.inl hEdge
  · exact Or.inr (hgoal hEdge)

end ABCTriple
end ABD2
