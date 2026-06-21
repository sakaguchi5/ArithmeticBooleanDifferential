import ABD.ABD3.Views.DPlusGraph.ProductObstruction.Step2ResidualProduct

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 3.

Both A-facing and B-facing C-residual products have the pointwise lower-bound
form extracted in Step 2.  This is the clean unabsorbed-product ledger consumed by
future product/radical bridge lemmas. -/
def CUnabsorbedProductLowerBound
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CResidualProductLowerBoundAgainstA P G R ∧
    T.CResidualProductLowerBoundAgainstB P G R

/-- Step 3 ledger obtained from the local product-obstruction input. -/
theorem cUnabsorbedProductLowerBound_of_productObstructionInput
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionInput P G R) :
    T.CUnabsorbedProductLowerBound P G R := by
  exact ⟨
    T.cResidualProductLowerBoundAgainstA_of_productObstructionInput P G R h,
    T.cResidualProductLowerBoundAgainstB_of_productObstructionInput P G R h⟩

/-- Product-obstruction input together with its derived unabsorbed-product lower
bound. -/
def CUnabsorbedProductWitness
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionInput P G R ∧
    T.CUnabsorbedProductLowerBound P G R

/-- The local input supplies the Step 3 unabsorbed-product witness. -/
theorem cUnabsorbedProductWitness_of_productObstructionInput
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionInput P G R) :
    T.CUnabsorbedProductWitness P G R := by
  exact ⟨h, T.cUnabsorbedProductLowerBound_of_productObstructionInput P G R h⟩

/-- Forget a Step 3 witness back to the local Step 1 product-obstruction input. -/
theorem productObstructionInput_of_cUnabsorbedProductWitness
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CUnabsorbedProductWitness P G R) :
    T.ProductObstructionInput P G R := by
  exact h.1

/-- Extract the lower-bound ledger from a Step 3 witness. -/
theorem cUnabsorbedProductLowerBound_of_witness
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CUnabsorbedProductWitness P G R) :
    T.CUnabsorbedProductLowerBound P G R := by
  exact h.2

/-- A named Step 3 goal.  Later files may strengthen this from the pointwise form
to a literal finite product or log-weighted product statement. -/
def ProductObstructionStep3Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CUnabsorbedProductLowerBound P G R

/-- The Step 3 goal follows from the local product-obstruction input. -/
theorem productObstructionStep3Goal_of_input
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionInput P G R) :
    T.ProductObstructionStep3Goal P G R := by
  exact T.cUnabsorbedProductLowerBound_of_productObstructionInput P G R h

end ABCData

end ABD3
