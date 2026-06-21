import ABD.ABD2.Regime.E2.Coverage

namespace ABD2
namespace ABCTriple

/-- The three scalar-synchronization edge types in the E2 graph.

* `AB`: the two-sided A/B cancellation edge;
* `AC`: an active A side synchronized with the C side;
* `BC`: an active B side synchronized with the C side.

At the current ABD2 level, the one-sided forced route does not yet distinguish
which of A or B is active internally, so `AC` and `BC` both project to the same
D2 common-scalar cost predicate.  This keeps the graph interface ready for a
later active-side refinement without changing the E2 coverage theorem. -/
inductive ScalarSyncEdge where
  | AB
  | AC
  | BC
  deriving DecidableEq, Repr

/-- An accepted scalar-synchronization edge.

This is the graph-language wrapper around the existing E2 common-scalar
witnesses.  The A/B edge is D1.  The active/C edges are D2. -/
def AcceptedScalarSyncEdge
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    ScalarSyncEdge → Prop
  | ScalarSyncEdge.AB =>
      ∃ t B : ℤ,
        0 ≤ B ∧
          B ^ data.N < ((T.c : ℤ) ^ data.M) ∧
            T.D1CommonScalarCostAtMost t B
  | ScalarSyncEdge.AC =>
      ∃ t B : ℤ,
        0 ≤ B ∧
          B ^ data.N < ((T.c : ℤ) ^ data.M) ∧
            T.GaugeOneSidedCommonScalarCostAtMost P T.coordinateGauge t B
  | ScalarSyncEdge.BC =>
      ∃ t B : ℤ,
        0 ≤ B ∧
          B ^ data.N < ((T.c : ℤ) ^ data.M) ∧
            T.GaugeOneSidedCommonScalarCostAtMost P T.coordinateGauge t B

/-- Existence of at least one accepted synchronization edge. -/
def HasAcceptedScalarSyncEdge
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) : Prop :=
  ∃ e : ScalarSyncEdge, T.AcceptedScalarSyncEdge P data e

/-- An accepted synchronization edge gives E2 common-scalar coverage. -/
theorem e2CommonScalarCoverage_of_acceptedScalarSyncEdge
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    {e : ScalarSyncEdge}
    (h : T.AcceptedScalarSyncEdge P data e) :
    T.E2CommonScalarCoverage P data := by
  cases e <;> rcases h with ⟨t, B, hBnonneg, hpow, hcost⟩
  · exact T.e2CommonScalarCoverage_of_d1CommonScalarCostAtMost P data
      hBnonneg hpow hcost
  · exact T.e2CommonScalarCoverage_of_d2CommonScalarCostAtMost P data
      hBnonneg hpow hcost
  · exact T.e2CommonScalarCoverage_of_d2CommonScalarCostAtMost P data
      hBnonneg hpow hcost

/-- An accepted synchronization edge exists iff E2 common-scalar coverage holds. -/
theorem hasAcceptedScalarSyncEdge_iff_e2CommonScalarCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData) :
    T.HasAcceptedScalarSyncEdge P data ↔ T.E2CommonScalarCoverage P data := by
  constructor
  · intro h
    rcases h with ⟨e, hedge⟩
    exact T.e2CommonScalarCoverage_of_acceptedScalarSyncEdge P data hedge
  · intro h
    rcases h with hD1 | hD2
    · rcases hD1 with ⟨t, B, hBnonneg, hpow, hcost⟩
      exact ⟨ScalarSyncEdge.AB, t, B, hBnonneg, hpow, hcost⟩
    · rcases hD2 with ⟨t, B, hBnonneg, hpow, hcost⟩
      exact ⟨ScalarSyncEdge.AC, t, B, hBnonneg, hpow, hcost⟩

/-- E2 coverage gives an accepted edge, choosing `AC` for the one-sided route
until the active side is refined further. -/
theorem acceptedScalarSyncEdge_of_e2CommonScalarCoverage
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.E2CommonScalarCoverage P data) :
    T.HasAcceptedScalarSyncEdge P data := by
  exact (T.hasAcceptedScalarSyncEdge_iff_e2CommonScalarCoverage P data).2 h

/-- An accepted edge gives E2 coverage. -/
theorem e2CommonScalarCoverage_of_hasAcceptedScalarSyncEdge
    (T : ABCTriple) (P : T.CImageProfile) (data : RationalPowerSavingData)
    (h : T.HasAcceptedScalarSyncEdge P data) :
    T.E2CommonScalarCoverage P data := by
  exact (T.hasAcceptedScalarSyncEdge_iff_e2CommonScalarCoverage P data).1 h

end ABCTriple
end ABD2
