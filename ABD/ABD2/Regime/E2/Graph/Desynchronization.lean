import ABD.ABD2.Regime.E2.Graph.Routes
import ABD.ABD2.Regime.E2.HardFrontier

namespace ABD2
namespace ABCTriple

/-- Scalar desynchronization: no edge of the A/B/C synchronization graph is
accepted.  This is the graph version of the E2 hard frontier. -/
def ScalarDesynchronization
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  ¬ T.HasAcceptedScalarSyncEdge P data

/-- Desynchronization is failure of graph route coverage. -/
theorem scalarDesynchronization_iff_not_routeCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.ScalarDesynchronization P data ↔
      ¬ T.ScalarSyncRouteCoverage P data := by
  constructor
  · intro h hroute
    exact h ((T.scalarSyncRouteCoverage_iff_hasAcceptedScalarSyncEdge P data).1 hroute)
  · intro h hEdge
    exact h ((T.scalarSyncRouteCoverage_iff_hasAcceptedScalarSyncEdge P data).2 hEdge)

/-- Desynchronization is exactly failure of E2 common-scalar coverage. -/
theorem scalarDesynchronization_iff_not_e2CommonScalarCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.ScalarDesynchronization P data ↔
      ¬ T.E2CommonScalarCoverage P data := by
  constructor
  · intro h hcov
    exact h ((T.hasAcceptedScalarSyncEdge_iff_e2CommonScalarCoverage P data).2 hcov)
  · intro h hEdge
    exact h ((T.hasAcceptedScalarSyncEdge_iff_e2CommonScalarCoverage P data).1 hEdge)

/-- The old E2 hard frontier is the same object as graph desynchronization. -/
theorem e2HardFrontier_iff_scalarDesynchronization
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.E2HardFrontier P data ↔ T.ScalarDesynchronization P data := by
  constructor
  · intro hfront
    exact (T.scalarDesynchronization_iff_not_e2CommonScalarCoverage P data).2
      (T.not_e2CommonScalarCoverage_of_e2HardFrontier P data hfront)
  · intro hdesync
    exact T.e2HardFrontier_of_not_e2CommonScalarCoverage P data
      ((T.scalarDesynchronization_iff_not_e2CommonScalarCoverage P data).1 hdesync)

/-- Build the hard frontier from graph desynchronization. -/
theorem e2HardFrontier_of_scalarDesynchronization
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.ScalarDesynchronization P data) :
    T.E2HardFrontier P data := by
  exact (T.e2HardFrontier_iff_scalarDesynchronization P data).2 h

/-- Read the hard frontier as graph desynchronization. -/
theorem scalarDesynchronization_of_e2HardFrontier
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2HardFrontier P data) :
    T.ScalarDesynchronization P data := by
  exact (T.e2HardFrontier_iff_scalarDesynchronization P data).1 h

end ABCTriple
end ABD2
