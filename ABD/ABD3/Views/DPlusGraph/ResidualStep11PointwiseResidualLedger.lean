import ABD.ABD3.Views.DPlusGraph.ResidualStep10CPortResidualSplit

namespace ABD3

namespace ABCData

/-- The C-port `p` is pointwise unabsorbed by A.

This keeps the surplus-port membership together with non-absorption by A.  Step C
uses this as one component of the residual ledger extracted from no accepted
arithmetic edge. -/
def CPortUnabsorbedByAAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  p ∈ T.CSurplusPorts P ∧ ¬ T.CPortAbsorbedByA P G R p

/-- The C-port `p` is pointwise unabsorbed by B.

This is the B-side companion to `CPortUnabsorbedByAAt`. -/
def CPortUnabsorbedByBAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  p ∈ T.CSurplusPorts P ∧ ¬ T.CPortAbsorbedByB P G R p

/-- Pointwise unabsorbed C-port data gives non-absorption by A. -/
theorem cPortUnabsorbedByAAt_of_unabsorbed
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) {p : ℕ}
    (h : T.CPortUnabsorbedAt P G R p) :
    T.CPortUnabsorbedByAAt P G R p := by
  unfold CPortUnabsorbedByAAt
  exact ⟨h.1, T.not_cPortAbsorbedByA_of_unabsorbed P G R h⟩

/-- Pointwise unabsorbed C-port data gives non-absorption by B. -/
theorem cPortUnabsorbedByBAt_of_unabsorbed
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) {p : ℕ}
    (h : T.CPortUnabsorbedAt P G R p) :
    T.CPortUnabsorbedByBAt P G R p := by
  unfold CPortUnabsorbedByBAt
  exact ⟨h.1, T.not_cPortAbsorbedByB_of_unabsorbed P G R h⟩

/-- Rejected-edge normal form gives pointwise non-absorption by A. -/
theorem cPortUnabsorbedByAAt_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.RejectedEdgeNormalForm P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortUnabsorbedByAAt P G R p := by
  exact T.cPortUnabsorbedByAAt_of_unabsorbed P G R
    (T.cPortUnabsorbedAt_of_rejectedEdgeNormalForm P G R h hp)

/-- Rejected-edge normal form gives pointwise non-absorption by B. -/
theorem cPortUnabsorbedByBAt_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.RejectedEdgeNormalForm P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortUnabsorbedByBAt P G R p := by
  exact T.cPortUnabsorbedByBAt_of_unabsorbed P G R
    (T.cPortUnabsorbedAt_of_rejectedEdgeNormalForm P G R h hp)

/-- No accepted arithmetic edge gives pointwise non-absorption by A. -/
theorem cPortUnabsorbedByAAt_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.NoAcceptedArithmeticEdge P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortUnabsorbedByAAt P G R p := by
  have hun : T.CPortUnabsorbedAt P G R p :=
    T.cPortUnabsorbedAt_of_absorptionLow P G R
      (T.cPortAbsorptionLow_of_noAcceptedArithmeticEdge P G R h) hp
  exact T.cPortUnabsorbedByAAt_of_unabsorbed P G R hun

/-- No accepted arithmetic edge gives pointwise non-absorption by B. -/
theorem cPortUnabsorbedByBAt_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.NoAcceptedArithmeticEdge P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortUnabsorbedByBAt P G R p := by
  have hun : T.CPortUnabsorbedAt P G R p :=
    T.cPortUnabsorbedAt_of_absorptionLow P G R
      (T.cPortAbsorptionLow_of_noAcceptedArithmeticEdge P G R h) hp
  exact T.cPortUnabsorbedByBAt_of_unabsorbed P G R hun

/-- Step C pointwise residual ledger at a positive C-surplus port.

This packages the useful local data extracted from `NoAcceptedArithmeticEdge`:

* the port is a positive C-surplus port;
* it is not absorbed by A;
* it is not absorbed by B;
* both A-C and B-C rejected edges have directed residual splits;
* consequently the port satisfies the C-residual-vs-active-residual dichotomy.

No product estimate is used here; this is still a local normal form. -/
def CPortPointwiseResidualLedgerAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  p ∈ T.CSurplusPorts P ∧
    T.CPortUnabsorbedByAAt P G R p ∧
    T.CPortUnabsorbedByBAt P G R p ∧
    T.CPortDirectedResidualSplitAt P G R p ∧
    T.CPortResidualOrientationDichotomy P G R p

/-- A pointwise unabsorbed C-port gives the full Step C ledger. -/
theorem cPortPointwiseResidualLedgerAt_of_unabsorbed
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) {p : ℕ}
    (h : T.CPortUnabsorbedAt P G R p) :
    T.CPortPointwiseResidualLedgerAt P G R p := by
  unfold CPortPointwiseResidualLedgerAt
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · exact T.cPortUnabsorbedByAAt_of_unabsorbed P G R h
  · exact T.cPortUnabsorbedByBAt_of_unabsorbed P G R h
  · exact T.cPortDirectedResidualSplitAt_of_unabsorbed P G R h
  · exact T.cPortResidualOrientationDichotomy_of_unabsorbed P G R h

/-- Rejected-edge normal form gives the full Step C ledger at every positive
C-surplus port. -/
theorem cPortPointwiseResidualLedgerAt_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.RejectedEdgeNormalForm P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortPointwiseResidualLedgerAt P G R p := by
  exact T.cPortPointwiseResidualLedgerAt_of_unabsorbed P G R
    (T.cPortUnabsorbedAt_of_rejectedEdgeNormalForm P G R h hp)

/-- No accepted arithmetic edge gives the full Step C ledger at every positive
C-surplus port. -/
theorem cPortPointwiseResidualLedgerAt_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.NoAcceptedArithmeticEdge P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortPointwiseResidualLedgerAt P G R p := by
  have hun : T.CPortUnabsorbedAt P G R p :=
    T.cPortUnabsorbedAt_of_absorptionLow P G R
      (T.cPortAbsorptionLow_of_noAcceptedArithmeticEdge P G R h) hp
  exact T.cPortPointwiseResidualLedgerAt_of_unabsorbed P G R hun

/-- The all-ports version of the Step C ledger. -/
def CPortPointwiseResidualLedgerAll
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ∀ p, p ∈ T.CSurplusPorts P → T.CPortPointwiseResidualLedgerAt P G R p

/-- Rejected-edge normal form gives the Step C ledger for all positive C-surplus
ports. -/
theorem cPortPointwiseResidualLedgerAll_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.RejectedEdgeNormalForm P G R) :
    T.CPortPointwiseResidualLedgerAll P G R := by
  intro p hp
  exact T.cPortPointwiseResidualLedgerAt_of_rejectedEdgeNormalForm P G R h hp

/-- No accepted arithmetic edge gives the Step C ledger for all positive C-surplus
ports. -/
theorem cPortPointwiseResidualLedgerAll_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.NoAcceptedArithmeticEdge P G R) :
    T.CPortPointwiseResidualLedgerAll P G R := by
  intro p hp
  exact T.cPortPointwiseResidualLedgerAt_of_noAcceptedArithmeticEdge P G R h hp

/-- Step C case predicate: at a positive C-surplus port, either the C-side
residual is high against both A and B, or some active A/B-side residual is high
against the C-port. -/
def CPortResidualCaseAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  p ∈ T.CSurplusPorts P ∧
    T.CPortResidualOrientationDichotomy P G R p

/-- The full Step C ledger contains the residual case predicate. -/
theorem cPortResidualCaseAt_of_pointwiseResidualLedgerAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) {p : ℕ}
    (h : T.CPortPointwiseResidualLedgerAt P G R p) :
    T.CPortResidualCaseAt P G R p := by
  unfold CPortPointwiseResidualLedgerAt CPortResidualCaseAt at *
  exact ⟨h.1, h.2.2.2.2⟩

/-- No accepted arithmetic edge gives the Step C residual case at every positive
C-surplus port. -/
theorem cPortResidualCaseAt_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.NoAcceptedArithmeticEdge P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortResidualCaseAt P G R p := by
  exact T.cPortResidualCaseAt_of_pointwiseResidualLedgerAt P G R
    (T.cPortPointwiseResidualLedgerAt_of_noAcceptedArithmeticEdge P G R h hp)

/-- A direct all-ports residual-case statement, extracted from no accepted edge. -/
theorem cPortResidualCase_all_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.NoAcceptedArithmeticEdge P G R) :
    ∀ p, p ∈ T.CSurplusPorts P → T.CPortResidualCaseAt P G R p := by
  intro p hp
  exact T.cPortResidualCaseAt_of_noAcceptedArithmeticEdge P G R h hp

end ABCData

end ABD3
