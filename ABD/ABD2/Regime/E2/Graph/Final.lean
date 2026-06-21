import ABD.ABD2.Regime.E2.Graph.DangerousBridge

namespace ABD2
namespace ABCTriple

/-- Step 7 final graph route goal: in the concrete dangerous zone, the
synchronization graph has route coverage, i.e. either the A/B cancellation route
or an active/C forcing route is open. -/
def E2GraphFinalRouteCoverageGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.E2ConcreteDangerNormalForm data → T.ScalarSyncRouteCoverage P data

/-- An accepted edge in the dangerous zone gives final graph route coverage. -/
theorem scalarSyncRouteCoverage_of_hasAcceptedScalarSyncEdge_of_concreteDanger
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hedge : T.HasAcceptedScalarSyncEdge P data)
    (_hnormal : T.E2ConcreteDangerNormalForm data) :
    T.ScalarSyncRouteCoverage P data := by
  exact (T.scalarSyncRouteCoverage_iff_hasAcceptedScalarSyncEdge P data).2 hedge

/-- Step 7 from Step 6: accepted-edge coverage in the dangerous zone gives route
coverage in the dangerous zone. -/
theorem e2GraphFinalRouteCoverageGoal_of_e2GraphDangerousAcceptedEdgeGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.E2GraphDangerousAcceptedEdgeGoal P data) :
    T.E2GraphFinalRouteCoverageGoal P data := by
  intro hnormal
  exact T.scalarSyncRouteCoverage_of_hasAcceptedScalarSyncEdge_of_concreteDanger P data
    (hgoal hnormal) hnormal

/-- Step 7 directly from the surplus-absorption target. -/
theorem scalarSyncRouteCoverage_of_scalarDesyncRadicalOrExceptionalGoal_of_concreteDanger
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.ScalarDesyncRadicalOrExceptionalGoal P data)
    (hnormal : T.E2ConcreteDangerNormalForm data) :
    T.ScalarSyncRouteCoverage P data := by
  have hedge : T.HasAcceptedScalarSyncEdge P data :=
    T.hasAcceptedScalarSyncEdge_of_scalarDesyncRadicalOrExceptionalGoal_of_concreteDanger
      P data hgoal hnormal
  exact (T.scalarSyncRouteCoverage_iff_hasAcceptedScalarSyncEdge P data).2 hedge

/-- The final graph route coverage goal follows from the surplus-absorption goal. -/
theorem e2GraphFinalRouteCoverageGoal_of_scalarDesyncRadicalOrExceptionalGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.ScalarDesyncRadicalOrExceptionalGoal P data) :
    T.E2GraphFinalRouteCoverageGoal P data := by
  intro hnormal
  exact T.scalarSyncRouteCoverage_of_scalarDesyncRadicalOrExceptionalGoal_of_concreteDanger
    P data hgoal hnormal

/-- The final graph route coverage goal follows from the pure radical
surplus-absorption goal. -/
theorem e2GraphFinalRouteCoverageGoal_of_forcesRadicalLargeGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.ScalarDesyncForcesRadicalLargeGoal P data) :
    T.E2GraphFinalRouteCoverageGoal P data := by
  exact T.e2GraphFinalRouteCoverageGoal_of_scalarDesyncRadicalOrExceptionalGoal P data
    (T.scalarDesyncRadicalOrExceptionalGoal_of_forcesRadicalLargeGoal P data hgoal)

/-- The final route coverage goal is equivalent to the existing concrete E2
coverage goal. -/
theorem e2GraphFinalRouteCoverageGoal_iff_e2ConcreteDangerCoverageGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2GraphFinalRouteCoverageGoal P data ↔
      T.E2ConcreteDangerCoverageGoal P data := by
  constructor
  · intro hroute hnormal
    exact T.e2CommonScalarCoverage_of_scalarSyncRouteCoverage P data
      (hroute hnormal)
  · intro hcoverage hnormal
    exact T.scalarSyncRouteCoverage_of_e2CommonScalarCoverage P data
      (hcoverage hnormal)

/-- The final graph route coverage goal is equivalent to the Step 6 accepted-edge
form. -/
theorem e2GraphFinalRouteCoverageGoal_iff_e2GraphDangerousAcceptedEdgeGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2GraphFinalRouteCoverageGoal P data ↔
      T.E2GraphDangerousAcceptedEdgeGoal P data := by
  constructor
  · intro hroute hnormal
    exact (T.scalarSyncRouteCoverage_iff_hasAcceptedScalarSyncEdge P data).1
      (hroute hnormal)
  · intro hedgeGoal
    exact T.e2GraphFinalRouteCoverageGoal_of_e2GraphDangerousAcceptedEdgeGoal P data
      hedgeGoal

/-- Final Step 7 theorem in E2 vocabulary: the surplus-absorption goal gives E2
common-scalar coverage over the concrete dangerous normal form. -/
theorem e2CommonScalarCoverage_of_scalarDesyncRadicalOrExceptionalGoal_of_concreteDanger
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.ScalarDesyncRadicalOrExceptionalGoal P data)
    (hnormal : T.E2ConcreteDangerNormalForm data) :
    T.E2CommonScalarCoverage P data := by
  exact T.e2CommonScalarCoverage_of_scalarSyncRouteCoverage P data
    (T.scalarSyncRouteCoverage_of_scalarDesyncRadicalOrExceptionalGoal_of_concreteDanger
      P data hgoal hnormal)

/-- Final Step 7 theorem as a reusable coverage goal. -/
theorem e2ConcreteDangerCoverageGoal_of_scalarDesyncRadicalOrExceptionalGoal
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (hgoal : T.ScalarDesyncRadicalOrExceptionalGoal P data) :
    T.E2ConcreteDangerCoverageGoal P data := by
  intro hnormal
  exact T.e2CommonScalarCoverage_of_scalarDesyncRadicalOrExceptionalGoal_of_concreteDanger
    P data hgoal hnormal

end ABCTriple
end ABD2
