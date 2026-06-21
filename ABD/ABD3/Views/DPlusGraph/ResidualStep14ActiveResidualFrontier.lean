import ABD.ABD3.Views.DPlusGraph.ResidualStep13AllCResidualRoute

namespace ABD3

namespace ABCData

/-- Step F pointwise A-active residual frontier at a positive C-surplus port.

The port is positive C-surplus, and the A-side residual is high against that
C-port.  This is the A-side half of the active-residual frontier. -/
def CPortActiveAResidualFrontierAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  p ∈ T.CSurplusPorts P ∧ T.AResidualHighAgainstCPort P G R p

/-- Step F pointwise B-active residual frontier at a positive C-surplus port.

The port is positive C-surplus, and the B-side residual is high against that
C-port. -/
def CPortActiveBResidualFrontierAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  p ∈ T.CSurplusPorts P ∧ T.BResidualHighAgainstCPort P G R p

/-- Ledger-preserving A-active residual frontier.

This is the part of the Step D/Step E active-residual frontier where an A-side
residual is responsible for the high cost at some positive C-surplus port. -/
def CSurplusActiveAResidualFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CPortPointwiseResidualLedgerAll P G R ∧
    ∃ p, T.CPortActiveAResidualFrontierAt P G R p

/-- Ledger-preserving B-active residual frontier. -/
def CSurplusActiveBResidualFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CPortPointwiseResidualLedgerAll P G R ∧
    ∃ p, T.CPortActiveBResidualFrontierAt P G R p

/-- Step F split of the active-residual frontier into A-active and B-active sides. -/
def CSurplusActiveResidualFrontierSplit
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CSurplusActiveAResidualFrontier P G R ∨
    T.CSurplusActiveBResidualFrontier P G R

/-- The Step D active-residual frontier splits into its A-active or B-active side.

No quantitative estimate is used here.  This is only the safe normal form needed
before later files decide whether an A/B-side residual can be converted into a
radical-tax contribution or must remain in the active-residual frontier. -/
theorem cSurplusActiveResidualFrontierSplit_of_activeResidualFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CSurplusActiveResidualFrontier P G R) :
    T.CSurplusActiveResidualFrontierSplit P G R := by
  unfold CSurplusActiveResidualFrontier CSurplusHasActiveResidualHigh at h
  rcases h with ⟨hledger, hhas⟩
  rcases hhas with ⟨p, hp, hactive⟩
  unfold CPortActiveResidualHighAgainstC at hactive
  rcases hactive with hA | hB
  · unfold CSurplusActiveResidualFrontierSplit
    left
    unfold CSurplusActiveAResidualFrontier CPortActiveAResidualFrontierAt
    exact ⟨hledger, ⟨p, hp, hA⟩⟩
  · unfold CSurplusActiveResidualFrontierSplit
    right
    unfold CSurplusActiveBResidualFrontier CPortActiveBResidualFrontierAt
    exact ⟨hledger, ⟨p, hp, hB⟩⟩

/-- The A-active residual frontier is a genuine active-residual frontier. -/
theorem activeResidualFrontier_of_activeAResidualFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CSurplusActiveAResidualFrontier P G R) :
    T.CSurplusActiveResidualFrontier P G R := by
  unfold CSurplusActiveAResidualFrontier CPortActiveAResidualFrontierAt at h
  rcases h with ⟨hledger, hA⟩
  rcases hA with ⟨p, hp, hres⟩
  unfold CSurplusActiveResidualFrontier CSurplusHasActiveResidualHigh
    CPortActiveResidualHighAgainstC
  exact ⟨hledger, ⟨p, hp, Or.inl hres⟩⟩

/-- The B-active residual frontier is a genuine active-residual frontier. -/
theorem activeResidualFrontier_of_activeBResidualFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CSurplusActiveBResidualFrontier P G R) :
    T.CSurplusActiveResidualFrontier P G R := by
  unfold CSurplusActiveBResidualFrontier CPortActiveBResidualFrontierAt at h
  rcases h with ⟨hledger, hB⟩
  rcases hB with ⟨p, hp, hres⟩
  unfold CSurplusActiveResidualFrontier CSurplusHasActiveResidualHigh
    CPortActiveResidualHighAgainstC
  exact ⟨hledger, ⟨p, hp, Or.inr hres⟩⟩

/-- The Step F split is equivalent to the existing active-residual frontier. -/
theorem cSurplusActiveResidualFrontierSplit_iff_activeResidualFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.CSurplusActiveResidualFrontierSplit P G R ↔
      T.CSurplusActiveResidualFrontier P G R := by
  constructor
  · intro h
    unfold CSurplusActiveResidualFrontierSplit at h
    rcases h with hA | hB
    · exact T.activeResidualFrontier_of_activeAResidualFrontier P G R hA
    · exact T.activeResidualFrontier_of_activeBResidualFrontier P G R hB
  · intro h
    exact T.cSurplusActiveResidualFrontierSplit_of_activeResidualFrontier P G R h

/-- A named Step F target: active residual tax candidate.

At this stage it is intentionally just the A/B split of the active-residual
frontier.  Later files may refine each side into an actual A-side or B-side
radical-tax contribution. -/
def CSurplusActiveResidualTaxCandidate
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CSurplusActiveResidualFrontierSplit P G R

/-- The active-residual frontier gives the named Step F tax-candidate input. -/
theorem cSurplusActiveResidualTaxCandidate_of_activeResidualFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CSurplusActiveResidualFrontier P G R) :
    T.CSurplusActiveResidualTaxCandidate P G R := by
  exact T.cSurplusActiveResidualFrontierSplit_of_activeResidualFrontier P G R h

/-- The named Step F tax-candidate input is still an active-residual frontier. -/
theorem activeResidualFrontier_of_activeResidualTaxCandidate
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CSurplusActiveResidualTaxCandidate P G R) :
    T.CSurplusActiveResidualFrontier P G R := by
  exact (T.cSurplusActiveResidualFrontierSplit_iff_activeResidualFrontier P G R).mp h

/-- Under no accepted arithmetic edge, the residual analysis now splits into the
Step E all-C/product-obstruction input or the Step F active-residual tax candidate.
-/
theorem productObstruction_or_activeResidualTaxCandidate_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.CSurplusUnabsorbedProductObstruction P G R ∨
      T.CSurplusActiveResidualTaxCandidate P G R := by
  have hsplit :=
    T.productObstruction_or_activeResidualFrontier_of_noAcceptedArithmeticEdge P G R hno
  rcases hsplit with hprod | hactive
  · exact Or.inl hprod
  · exact Or.inr
      (T.cSurplusActiveResidualTaxCandidate_of_activeResidualFrontier P G R hactive)

/-- If the product-obstruction side is absent, no accepted edge forces the Step F
active-residual tax-candidate side. -/
theorem activeResidualTaxCandidate_of_noAcceptedArithmeticEdge_of_not_productObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R)
    (hnot : ¬ T.CSurplusUnabsorbedProductObstruction P G R) :
    T.CSurplusActiveResidualTaxCandidate P G R := by
  have hsplit :=
    T.productObstruction_or_activeResidualTaxCandidate_of_noAcceptedArithmeticEdge P G R hno
  rcases hsplit with hprod | htax
  · exfalso
    exact hnot hprod
  · exact htax

end ABCData

end ABD3
