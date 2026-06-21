import ABD.ABD3.Views.DPlusGraph.ResidualStep11PointwiseResidualLedger

namespace ABD3

namespace ABCData

/-- Step D, all-C-residual side.

Every positive C-surplus port has C-side residual high against both A and B.  This
is the clean entry condition for the later surplus-absorption/product argument:
all C-surplus ports remain unabsorbed in the directed C-residual direction. -/
def CSurplusAllCResidualHighAgainstBoth
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ∀ p, p ∈ T.CSurplusPorts P →
    T.CPortCResidualHighAgainstBoth P G R p

/-- Step D, active-residual frontier side.

At least one positive C-surplus port has an active A/B-side residual high against
that C-port.  This is the complementary frontier to the all-C-residual case. -/
def CSurplusHasActiveResidualHigh
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ∃ p, p ∈ T.CSurplusPorts P ∧
    T.CPortActiveResidualHighAgainstC P G R p

/-- Step D global residual dichotomy.

After Step C has produced a pointwise residual ledger for every positive
C-surplus port, the global situation splits into exactly the two useful routes:

* all C-surplus ports are C-residual-high against both A and B;
* or some port falls into the active A/B residual frontier.

No product estimate is asserted here.  This is only the clean finite/global
case split that prepares the later absorption analysis. -/
def CSurplusResidualGlobalDichotomy
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CSurplusAllCResidualHighAgainstBoth P G R ∨
    T.CSurplusHasActiveResidualHigh P G R

/-- Extract the C-residual-high fact from the all-C-residual side. -/
theorem cPortCResidualHighAgainstBoth_of_allCResidualHigh
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.CSurplusAllCResidualHighAgainstBoth P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortCResidualHighAgainstBoth P G R p :=
  h p hp

/-- Step C pointwise ledgers imply the Step D global dichotomy. -/
theorem cSurplusResidualGlobalDichotomy_of_pointwiseResidualLedgerAll
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hledger : T.CPortPointwiseResidualLedgerAll P G R) :
    T.CSurplusResidualGlobalDichotomy P G R := by
  classical
  by_cases hall : T.CSurplusAllCResidualHighAgainstBoth P G R
  · exact Or.inl hall
  · right
    by_contra hactive
    apply hall
    intro p hp
    have hpoint : T.CPortPointwiseResidualLedgerAt P G R p :=
      hledger p hp
    have hcase : T.CPortResidualCaseAt P G R p :=
      T.cPortResidualCaseAt_of_pointwiseResidualLedgerAt P G R hpoint
    have horient : T.CPortResidualOrientationDichotomy P G R p := hcase.2
    unfold CPortResidualOrientationDichotomy at horient
    rcases horient with hC | hAB
    · exact hC
    · exfalso
      exact hactive ⟨p, hp, hAB⟩

/-- Rejected-edge normal form gives the Step D global residual dichotomy. -/
theorem cSurplusResidualGlobalDichotomy_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.RejectedEdgeNormalForm P G R) :
    T.CSurplusResidualGlobalDichotomy P G R := by
  exact T.cSurplusResidualGlobalDichotomy_of_pointwiseResidualLedgerAll P G R
    (T.cPortPointwiseResidualLedgerAll_of_rejectedEdgeNormalForm P G R h)

/-- No accepted arithmetic edge gives the Step D global residual dichotomy. -/
theorem cSurplusResidualGlobalDichotomy_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.NoAcceptedArithmeticEdge P G R) :
    T.CSurplusResidualGlobalDichotomy P G R := by
  exact T.cSurplusResidualGlobalDichotomy_of_pointwiseResidualLedgerAll P G R
    (T.cPortPointwiseResidualLedgerAll_of_noAcceptedArithmeticEdge P G R h)

/-- Ledger-preserving all-C-residual route.

This packages the Step C pointwise ledger together with the all-C-residual side,
so later product/absorption files can use both the local normal form and the
chosen global branch without re-extracting anything. -/
def CSurplusAllCResidualRoute
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CPortPointwiseResidualLedgerAll P G R ∧
    T.CSurplusAllCResidualHighAgainstBoth P G R

/-- Ledger-preserving active-residual frontier route. -/
def CSurplusActiveResidualFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CPortPointwiseResidualLedgerAll P G R ∧
    T.CSurplusHasActiveResidualHigh P G R

/-- Ledger-preserving Step D branch split. -/
def CSurplusResidualRouteDichotomy
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CSurplusAllCResidualRoute P G R ∨
    T.CSurplusActiveResidualFrontier P G R

/-- Pointwise ledgers give the ledger-preserving Step D route split. -/
theorem cSurplusResidualRouteDichotomy_of_pointwiseResidualLedgerAll
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hledger : T.CPortPointwiseResidualLedgerAll P G R) :
    T.CSurplusResidualRouteDichotomy P G R := by
  have hdich : T.CSurplusResidualGlobalDichotomy P G R :=
    T.cSurplusResidualGlobalDichotomy_of_pointwiseResidualLedgerAll P G R hledger
  unfold CSurplusResidualGlobalDichotomy at hdich
  rcases hdich with hall | hactive
  · exact Or.inl ⟨hledger, hall⟩
  · exact Or.inr ⟨hledger, hactive⟩

/-- Rejected-edge normal form gives the ledger-preserving Step D route split. -/
theorem cSurplusResidualRouteDichotomy_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.RejectedEdgeNormalForm P G R) :
    T.CSurplusResidualRouteDichotomy P G R := by
  exact T.cSurplusResidualRouteDichotomy_of_pointwiseResidualLedgerAll P G R
    (T.cPortPointwiseResidualLedgerAll_of_rejectedEdgeNormalForm P G R h)

/-- No accepted arithmetic edge gives the ledger-preserving Step D route split. -/
theorem cSurplusResidualRouteDichotomy_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.NoAcceptedArithmeticEdge P G R) :
    T.CSurplusResidualRouteDichotomy P G R := by
  exact T.cSurplusResidualRouteDichotomy_of_pointwiseResidualLedgerAll P G R
    (T.cPortPointwiseResidualLedgerAll_of_noAcceptedArithmeticEdge P G R h)

end ABCData

end ABD3
