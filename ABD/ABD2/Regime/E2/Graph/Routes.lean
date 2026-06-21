import ABD.ABD2.Regime.E2.Graph.Edge

namespace ABD2
namespace ABCTriple

/-- The A/B cancellation route in graph language: the A-B edge is accepted. -/
def ABCancellationRoute
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.AcceptedScalarSyncEdge P data ScalarSyncEdge.AB

/-- The active/C forced route in graph language: either active-C edge is accepted.

At this layer, `AC` and `BC` both map to the current one-sided D2 predicate; the
split is deliberately recorded so future files can attach active-side data. -/
def CForcingRoute
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.AcceptedScalarSyncEdge P data ScalarSyncEdge.AC ∨
    T.AcceptedScalarSyncEdge P data ScalarSyncEdge.BC

/-- Route-level graph coverage. -/
def ScalarSyncRouteCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  T.ABCancellationRoute P data ∨ T.CForcingRoute P data

/-- Route coverage is equivalent to having an accepted edge. -/
theorem scalarSyncRouteCoverage_iff_hasAcceptedScalarSyncEdge
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.ScalarSyncRouteCoverage P data ↔
      T.HasAcceptedScalarSyncEdge P data := by
  constructor
  · intro h
    rcases h with hAB | hC
    · exact ⟨ScalarSyncEdge.AB, hAB⟩
    · rcases hC with hAC | hBC
      · exact ⟨ScalarSyncEdge.AC, hAC⟩
      · exact ⟨ScalarSyncEdge.BC, hBC⟩
  · intro h
    rcases h with ⟨e, hedge⟩
    cases e
    · exact Or.inl hedge
    · exact Or.inr (Or.inl hedge)
    · exact Or.inr (Or.inr hedge)

/-- Route coverage is equivalent to existing E2 common-scalar coverage. -/
theorem scalarSyncRouteCoverage_iff_e2CommonScalarCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.ScalarSyncRouteCoverage P data ↔ T.E2CommonScalarCoverage P data := by
  calc
    T.ScalarSyncRouteCoverage P data
        ↔ T.HasAcceptedScalarSyncEdge P data :=
          T.scalarSyncRouteCoverage_iff_hasAcceptedScalarSyncEdge P data
    _   ↔ T.E2CommonScalarCoverage P data :=
          T.hasAcceptedScalarSyncEdge_iff_e2CommonScalarCoverage P data

/-- A/B accepted edge opens the A/B cancellation route. -/
theorem aBCancellationRoute_of_acceptedABEdge
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.AcceptedScalarSyncEdge P data ScalarSyncEdge.AB) :
    T.ABCancellationRoute P data := by
  exact h

/-- Active/C accepted edge opens the C-forcing route. -/
theorem cForcingRoute_of_acceptedACEdge
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.AcceptedScalarSyncEdge P data ScalarSyncEdge.AC) :
    T.CForcingRoute P data := by
  exact Or.inl h

/-- Active/C accepted edge opens the C-forcing route. -/
theorem cForcingRoute_of_acceptedBCEdge
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.AcceptedScalarSyncEdge P data ScalarSyncEdge.BC) :
    T.CForcingRoute P data := by
  exact Or.inr h

/-- Any graph route coverage enters the existing E2 coverage. -/
theorem e2CommonScalarCoverage_of_scalarSyncRouteCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.ScalarSyncRouteCoverage P data) :
    T.E2CommonScalarCoverage P data := by
  exact (T.scalarSyncRouteCoverage_iff_e2CommonScalarCoverage P data).1 h

/-- Existing E2 coverage can be read as route coverage in the synchronization graph. -/
theorem scalarSyncRouteCoverage_of_e2CommonScalarCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2CommonScalarCoverage P data) :
    T.ScalarSyncRouteCoverage P data := by
  exact (T.scalarSyncRouteCoverage_iff_e2CommonScalarCoverage P data).2 h

end ABCTriple
end ABD2
