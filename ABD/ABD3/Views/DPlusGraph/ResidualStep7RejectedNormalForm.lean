import ABD.ABD3.Views.DPlusGraph.ResidualStep6UnitBoundary

namespace ABD3

namespace ABCData

/-- Step 8 rejected-edge normal form.

This deliberately records only the local, pointwise information: the A-B edge is
rejected, and every positive C-port is rejected by both A and B.  It does not use
any product-dominance information; that belongs to Step 9. -/
def RejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ABEdgeRejected P G R ∧
    ∀ p, p ∈ T.CSurplusPorts P → T.CPortUnabsorbedAt P G R p

/-- No accepted arithmetic edge gives the rejected-edge normal form. -/
theorem rejectedEdgeNormalForm_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.RejectedEdgeNormalForm P G R := by
  unfold RejectedEdgeNormalForm
  constructor
  · exact T.abEdgeRejected_of_noAcceptedArithmeticEdge P G R hno
  · intro p hp
    exact T.cPortUnabsorbedAt_of_absorptionLow P G R
      (T.cPortAbsorptionLow_of_noAcceptedArithmeticEdge P G R hno) hp

/-- The rejected-edge normal form is exactly the existing no-accepted-edge
predicate. -/
theorem noAcceptedArithmeticEdge_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.RejectedEdgeNormalForm P G R) :
    T.NoAcceptedArithmeticEdge P G R := by
  unfold RejectedEdgeNormalForm at h
  unfold NoAcceptedArithmeticEdge CPortAbsorptionLow
  exact ⟨h.1, h.2⟩

/-- Step 8 equivalence.  This is the safe normal-form theorem: it unfolds the
local rejected-edge content without touching product dominance. -/
theorem rejectedEdgeNormalForm_iff_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.RejectedEdgeNormalForm P G R ↔ T.NoAcceptedArithmeticEdge P G R := by
  constructor
  · exact T.noAcceptedArithmeticEdge_of_rejectedEdgeNormalForm P G R
  · exact T.rejectedEdgeNormalForm_of_noAcceptedArithmeticEdge P G R

/-- Pointwise C-port rejection by A, extracted from the normal form. -/
theorem not_cPortAbsorbedByA_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.RejectedEdgeNormalForm P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    ¬ T.CPortAbsorbedByA P G R p := by
  exact T.not_cPortAbsorbedByA_of_unabsorbed P G R (h.2 p hp)

/-- Pointwise C-port rejection by B, extracted from the normal form. -/
theorem not_cPortAbsorbedByB_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.RejectedEdgeNormalForm P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    ¬ T.CPortAbsorbedByB P G R p := by
  exact T.not_cPortAbsorbedByB_of_unabsorbed P G R (h.2 p hp)

/-- The normal form contains the A-B rejected edge. -/
theorem abEdgeRejected_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.RejectedEdgeNormalForm P G R) :
    T.ABEdgeRejected P G R :=
  h.1

/-- The normal form contains pointwise unabsorbed positive C-ports. -/
theorem cPortUnabsorbedAt_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.RejectedEdgeNormalForm P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortUnabsorbedAt P G R p :=
  h.2 p hp

end ABCData

end ABD3
