import ABD.ABD2.Regime.E2.Graph.SurplusAbsorption
import ABD.ABD2.Regime.E2.ConcreteDangerNormalForm

namespace ABD2
namespace ABCTriple

/-- Step 6 graph goal: in the concrete dangerous zone, some synchronization edge
must be accepted.

This is the graph-language form of dangerous-zone coverage before converting the
accepted edge back into the route/E2 vocabulary. -/
def E2GraphDangerousAcceptedEdgeGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.E2ConcreteDangerNormalForm data → T.HasAcceptedScalarSyncEdge P data

/-- Step 6 bridge.

If graph desynchronization always falls to the harmless side
`radical-large ∨ exceptional`, then a concrete dangerous triple cannot be
scalar-desynchronized.  Hence it has an accepted synchronization edge. -/
theorem hasAcceptedScalarSyncEdge_of_scalarDesyncRadicalOrExceptionalGoal_of_concreteDanger
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.ScalarDesyncRadicalOrExceptionalGoal P data)
    (hnormal : T.E2ConcreteDangerNormalForm data) :
    T.HasAcceptedScalarSyncEdge P data := by
  by_cases hEdge : T.HasAcceptedScalarSyncEdge P data
  · exact hEdge
  · have hdesync : T.ScalarDesynchronization P data := hEdge
    have hbad : T.E2RadicalLarge data ∨ T.E2PastenExceptionalPattern :=
      hgoal hdesync
    rcases hbad with hlarge | hexceptional
    · have hnotLarge : ¬ T.E2RadicalLarge data :=
        (T.e2RadicalSmallInequality_iff_not_radicalLarge data).1 hnormal.1
      exact False.elim (hnotLarge hlarge)
    · have hnotExceptional : ¬ T.E2PastenExceptionalPattern :=
        (T.e2NonExceptionalPattern_iff_not_exceptional).1 hnormal.2
      exact False.elim (hnotExceptional hexceptional)

/-- A surplus-absorption goal supplies the Step 6 accepted-edge goal. -/
theorem e2GraphDangerousAcceptedEdgeGoal_of_scalarDesyncRadicalOrExceptionalGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.ScalarDesyncRadicalOrExceptionalGoal P data) :
    T.E2GraphDangerousAcceptedEdgeGoal P data := by
  intro hnormal
  exact T.hasAcceptedScalarSyncEdge_of_scalarDesyncRadicalOrExceptionalGoal_of_concreteDanger
    P data hgoal hnormal

/-- The pure radical surplus-absorption goal is enough for Step 6. -/
theorem e2GraphDangerousAcceptedEdgeGoal_of_forcesRadicalLargeGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.ScalarDesyncForcesRadicalLargeGoal P data) :
    T.E2GraphDangerousAcceptedEdgeGoal P data := by
  exact T.e2GraphDangerousAcceptedEdgeGoal_of_scalarDesyncRadicalOrExceptionalGoal P data
    (T.scalarDesyncRadicalOrExceptionalGoal_of_forcesRadicalLargeGoal P data hgoal)

/-- The accepted-edge dangerous-zone goal is equivalent to the existing concrete
E2 dangerous coverage goal. -/
theorem e2GraphDangerousAcceptedEdgeGoal_iff_e2ConcreteDangerCoverageGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2GraphDangerousAcceptedEdgeGoal P data ↔
      T.E2ConcreteDangerCoverageGoal P data := by
  constructor
  · intro hEdgeGoal hnormal
    exact T.e2CommonScalarCoverage_of_hasAcceptedScalarSyncEdge P data
      (hEdgeGoal hnormal)
  · intro hCoverage hnormal
    exact T.acceptedScalarSyncEdge_of_e2CommonScalarCoverage P data
      (hCoverage hnormal)

/-- The Step 6 graph goal is also equivalent to the concrete radical-reduction
form, via the existing E2 normal-form theorem. -/
theorem e2GraphDangerousAcceptedEdgeGoal_iff_e2ConcreteRadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2GraphDangerousAcceptedEdgeGoal P data ↔
      T.E2ConcreteRadicalReductionGoal P data := by
  calc
    T.E2GraphDangerousAcceptedEdgeGoal P data
        ↔ T.E2ConcreteDangerCoverageGoal P data :=
          T.e2GraphDangerousAcceptedEdgeGoal_iff_e2ConcreteDangerCoverageGoal P data
    _   ↔ T.E2ConcreteRadicalReductionGoal P data :=
          T.e2ConcreteDangerCoverageGoal_iff_e2ConcreteRadicalReductionGoal P data

/-- Read an existing concrete radical-reduction theorem as the Step 6 graph goal. -/
theorem e2GraphDangerousAcceptedEdgeGoal_of_e2ConcreteRadicalReductionGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.E2ConcreteRadicalReductionGoal P data) :
    T.E2GraphDangerousAcceptedEdgeGoal P data := by
  exact (T.e2GraphDangerousAcceptedEdgeGoal_iff_e2ConcreteRadicalReductionGoal P data).2
    hgoal

/-- Step 6 graph goal gives the existing concrete radical-reduction theorem. -/
theorem e2ConcreteRadicalReductionGoal_of_e2GraphDangerousAcceptedEdgeGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.E2GraphDangerousAcceptedEdgeGoal P data) :
    T.E2ConcreteRadicalReductionGoal P data := by
  exact (T.e2GraphDangerousAcceptedEdgeGoal_iff_e2ConcreteRadicalReductionGoal P data).1
    hgoal

end ABCTriple
end ABD2
