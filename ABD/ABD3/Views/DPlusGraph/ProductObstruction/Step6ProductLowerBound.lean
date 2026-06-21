import ABD.ABD3.Views.DPlusGraph.ProductObstruction.Step5SpecialCases

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 6.

The literal finite-product lower-bound ledger.  Step 2 deliberately kept the safe
output in pointwise form; this file closes the purely finite-product API step and
turns those pointwise inequalities into actual product inequalities. -/
def CResidualLiteralProductLowerBound
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CResidualProductAgainstALowerBoundGoal P G R ∧
    T.CResidualProductAgainstBLowerBoundGoal P G R

/-- Pointwise A-facing lower bounds imply the literal A-facing residual-product
lower bound. -/
theorem cResidualProductAgainstALowerBoundGoal_of_pointwiseLowerBound
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CResidualProductLowerBoundAgainstA P G R) :
    T.CResidualProductAgainstALowerBoundGoal P G R := by
  unfold CResidualProductAgainstALowerBoundGoal CResidualBaselineProduct
    CResidualProductAgainstA
  refine Finset.prod_le_prod ?hNonneg ?hPointwise
  · intro p hp
    exact Nat.zero_le (R + 1)
  · intro p hp
    exact h p hp

/-- Pointwise B-facing lower bounds imply the literal B-facing residual-product
lower bound. -/
theorem cResidualProductAgainstBLowerBoundGoal_of_pointwiseLowerBound
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CResidualProductLowerBoundAgainstB P G R) :
    T.CResidualProductAgainstBLowerBoundGoal P G R := by
  unfold CResidualProductAgainstBLowerBoundGoal CResidualBaselineProduct
    CResidualProductAgainstB
  refine Finset.prod_le_prod ?hNonneg ?hPointwise
  · intro p hp
    exact Nat.zero_le (R + 1)
  · intro p hp
    exact h p hp

/-- The Step 3 unabsorbed-product lower-bound ledger supplies the literal
finite-product lower-bound ledger. -/
theorem cResidualLiteralProductLowerBound_of_unabsorbedProductLowerBound
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CUnabsorbedProductLowerBound P G R) :
    T.CResidualLiteralProductLowerBound P G R := by
  exact ⟨
    T.cResidualProductAgainstALowerBoundGoal_of_pointwiseLowerBound P G R h.1,
    T.cResidualProductAgainstBLowerBoundGoal_of_pointwiseLowerBound P G R h.2⟩

/-- Product-obstruction input gives the literal finite-product lower-bound
ledger. -/
theorem cResidualLiteralProductLowerBound_of_productObstructionInput
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionInput P G R) :
    T.CResidualLiteralProductLowerBound P G R := by
  exact T.cResidualLiteralProductLowerBound_of_unabsorbedProductLowerBound P G R
    (T.cUnabsorbedProductLowerBound_of_productObstructionInput P G R h)

/-- Product-obstruction input together with the literal product lower-bound
ledger. -/
def CResidualLiteralProductWitness
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionInput P G R ∧
    T.CResidualLiteralProductLowerBound P G R

/-- The local product-obstruction input supplies the Step 6 literal-product
witness. -/
theorem cResidualLiteralProductWitness_of_productObstructionInput
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionInput P G R) :
    T.CResidualLiteralProductWitness P G R := by
  exact ⟨h, T.cResidualLiteralProductLowerBound_of_productObstructionInput P G R h⟩

/-- Forget a Step 6 literal-product witness back to the local Step 1 input. -/
theorem productObstructionInput_of_cResidualLiteralProductWitness
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CResidualLiteralProductWitness P G R) :
    T.ProductObstructionInput P G R := by
  exact h.1

/-- Extract the literal product lower-bound ledger from a Step 6 witness. -/
theorem cResidualLiteralProductLowerBound_of_witness
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CResidualLiteralProductWitness P G R) :
    T.CResidualLiteralProductLowerBound P G R := by
  exact h.2

/-- A literal-product-to-radical-large bridge target.

This is a stronger, product-shaped alternative to the Step 4 pointwise bridge:
instead of consuming `CUnabsorbedProductLowerBound`, it consumes the literal
finite-product lower bounds proved in Step 6. -/
def CResidualLiteralProductToRadicalLargeBridgeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CResidualLiteralProductLowerBound P G R → T.RadicalLarge P

/-- A literal product bridge is enough to solve the direct product-obstruction to
radical-large goal. -/
theorem productObstructionToRadicalLargeGoal_of_literalProductBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hbridge : T.CResidualLiteralProductToRadicalLargeBridgeGoal P G R) :
    T.ProductObstructionToRadicalLargeGoal P G R := by
  intro hinput
  exact hbridge
    (T.cResidualLiteralProductLowerBound_of_productObstructionInput P G R hinput)

/-- The literal product bridge also supplies the named Step 4 radical-large goal. -/
theorem productObstructionStep4Goal_of_literalProductBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hbridge : T.CResidualLiteralProductToRadicalLargeBridgeGoal P G R) :
    T.ProductObstructionStep4Goal P G R := by
  exact T.productObstructionToRadicalLargeGoal_of_literalProductBridge P G R hbridge

/-- Step 6 named target: product-obstruction input supplies literal finite-product
lower bounds. -/
def ProductObstructionStep6Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CResidualLiteralProductLowerBound P G R

/-- The Step 3 pointwise ledger supplies the named Step 6 goal. -/
theorem productObstructionStep6Goal_of_step3Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionStep3Goal P G R) :
    T.ProductObstructionStep6Goal P G R := by
  exact T.cResidualLiteralProductLowerBound_of_unabsorbedProductLowerBound P G R h

/-- The local product-obstruction input supplies the named Step 6 goal. -/
theorem productObstructionStep6Goal_of_input
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionInput P G R) :
    T.ProductObstructionStep6Goal P G R := by
  exact T.cResidualLiteralProductLowerBound_of_productObstructionInput P G R h

/-- Step 6 bridge target: it remains to turn the literal product lower-bound
ledger into radical-large. -/
def ProductObstructionStep6BridgeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CResidualLiteralProductToRadicalLargeBridgeGoal P G R

/-- The Step 6 bridge target supplies the Step 4 radical-large route. -/
theorem productObstructionStep4Goal_of_step6BridgeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionStep6BridgeGoal P G R) :
    T.ProductObstructionStep4Goal P G R := by
  exact T.productObstructionStep4Goal_of_literalProductBridge P G R h

end ABCData

end ABD3
