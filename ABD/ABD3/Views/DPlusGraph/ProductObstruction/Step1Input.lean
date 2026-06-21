import ABD.ABD3.Views.DPlusGraph.ResidualStep14ActiveResidualFrontier

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 1.

This is the reset entry point for the new `ProductObstruction` subfolder.  It
renames the previously isolated all-C-residual/product-obstruction branch into a
local input for the product-obstruction attack.

No new product inequality is asserted here.  The point of this file is to keep the
new route independent and give later steps a stable, folder-local name to consume.
-/
def ProductObstructionInput
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CSurplusUnabsorbedProductObstruction P G R

/-- Step 1 input is exactly the upstream unabsorbed product obstruction. -/
theorem productObstructionInput_iff_unabsorbedProductObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.ProductObstructionInput P G R ↔
      T.CSurplusUnabsorbedProductObstruction P G R := by
  rfl

/-- Upstream product obstruction gives the local Step 1 input. -/
theorem productObstructionInput_of_unabsorbedProductObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CSurplusUnabsorbedProductObstruction P G R) :
    T.ProductObstructionInput P G R := by
  exact h

/-- The local Step 1 input can be forgotten back to the upstream product
obstruction. -/
theorem unabsorbedProductObstruction_of_productObstructionInput
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionInput P G R) :
    T.CSurplusUnabsorbedProductObstruction P G R := by
  exact h

/-- Product-obstruction input contains the Step C pointwise ledger. -/
theorem cPortPointwiseResidualLedgerAll_of_productObstructionInput
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionInput P G R) :
    T.CPortPointwiseResidualLedgerAll P G R := by
  exact T.cPortPointwiseResidualLedgerAll_of_productObstruction P G R h

/-- Product-obstruction input gives C-residual-high against A at every positive
C-surplus port. -/
theorem cResidualHighAgainstA_of_productObstructionInput
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.ProductObstructionInput P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CResidualHighAgainstA P G R p := by
  exact T.cResidualHighAgainstA_of_productObstruction P G R h hp

/-- Product-obstruction input gives C-residual-high against B at every positive
C-surplus port. -/
theorem cResidualHighAgainstB_of_productObstructionInput
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.ProductObstructionInput P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CResidualHighAgainstB P G R p := by
  exact T.cResidualHighAgainstB_of_productObstruction P G R h hp

/-- Product-obstruction input gives paired C-residual-high data at every positive
C-surplus port. -/
theorem cPortCResidualHighAgainstBoth_of_productObstructionInput
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.ProductObstructionInput P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortCResidualHighAgainstBoth P G R p := by
  exact T.cPortCResidualHighAgainstBoth_of_productObstruction P G R h hp

/-- The local Step 1 split from the no-accepted-edge normal form.

Either the new product-obstruction route receives its input, or the already
separated active-residual tax candidate remains as the complementary branch. -/
theorem productObstructionInput_or_activeResidualTaxCandidate_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.ProductObstructionInput P G R ∨
      T.CSurplusActiveResidualTaxCandidate P G R := by
  have hsplit :=
    T.productObstruction_or_activeResidualTaxCandidate_of_noAcceptedArithmeticEdge P G R hno
  rcases hsplit with hprod | htax
  · exact Or.inl (T.productObstructionInput_of_unabsorbedProductObstruction P G R hprod)
  · exact Or.inr htax

/-- If no accepted edge holds and the active-residual tax side is absent, then the
new product-obstruction route receives its input. -/
theorem productObstructionInput_of_noAcceptedArithmeticEdge_of_not_activeResidualTaxCandidate
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R)
    (hnot : ¬ T.CSurplusActiveResidualTaxCandidate P G R) :
    T.ProductObstructionInput P G R := by
  have hsplit :=
    T.productObstructionInput_or_activeResidualTaxCandidate_of_noAcceptedArithmeticEdge P G R hno
  rcases hsplit with hprod | htax
  · exact hprod
  · exfalso
    exact hnot htax

/-- A named placeholder for the first target of the product-obstruction route.

Later steps should replace this alias by an actual product lower-bound statement,
while keeping upstream Step 1 unchanged. -/
def ProductObstructionStep1Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionInput P G R

/-- The local input supplies the named Step 1 goal. -/
theorem productObstructionStep1Goal_of_input
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionInput P G R) :
    T.ProductObstructionStep1Goal P G R := by
  exact h

end ABCData

end ABD3
