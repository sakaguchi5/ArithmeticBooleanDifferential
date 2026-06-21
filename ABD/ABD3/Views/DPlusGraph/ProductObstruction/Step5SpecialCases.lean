import ABD.ABD3.Views.DPlusGraph.ProductObstruction.Step4ProductBridgeGoal

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 5A: no positive C-surplus port.

This is a boundary/sanity case for the product route.  It is kept as a separate
case because future work may prove it impossible under `RadicalSmall`, but this
file does not assert that stronger fact. -/
def ProductObstructionNoPortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  (T.CSurplusPorts P).card = 0 ∧ T.ProductObstructionInput P G R

/-- Product-obstruction route, Step 5B: exactly one positive C-surplus port. -/
def ProductObstructionSinglePortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  (T.CSurplusPorts P).card = 1 ∧ T.ProductObstructionInput P G R

/-- Product-obstruction route, Step 5C: at least two positive C-surplus ports. -/
def ProductObstructionMultiPortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  2 ≤ (T.CSurplusPorts P).card ∧ T.ProductObstructionInput P G R

/-- The special-case split for the product-obstruction route. -/
def ProductObstructionSpecialCaseSplit
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionNoPortCase P G R ∨
    T.ProductObstructionSinglePortCase P G R ∨
      T.ProductObstructionMultiPortCase P G R

/-- Every product-obstruction input falls into the no-port, one-port, or multi-port
case. -/
theorem productObstructionSpecialCaseSplit_of_input
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionInput P G R) :
    T.ProductObstructionSpecialCaseSplit P G R := by
  unfold ProductObstructionSpecialCaseSplit
  by_cases h0 : (T.CSurplusPorts P).card = 0
  · exact Or.inl ⟨h0, h⟩
  · by_cases h1 : (T.CSurplusPorts P).card = 1
    · exact Or.inr (Or.inl ⟨h1, h⟩)
    · have h2 : 2 ≤ (T.CSurplusPorts P).card := by
        omega
      exact Or.inr (Or.inr ⟨h2, h⟩)

/-- The no-port special case bridge target. -/
def ProductObstructionNoPortBridgeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionNoPortCase P G R → T.RadicalLarge P

/-- The single-port special case bridge target. -/
def ProductObstructionSinglePortBridgeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionSinglePortCase P G R → T.RadicalLarge P

/-- The multi-port special case bridge target. -/
def ProductObstructionMultiPortBridgeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionMultiPortCase P G R → T.RadicalLarge P

/-- If each special case has a radical-large bridge, then the whole
product-obstruction route has the radical-large goal. -/
theorem productObstructionToRadicalLargeGoal_of_specialCaseBridges
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h0 : T.ProductObstructionNoPortBridgeGoal P G R)
    (h1 : T.ProductObstructionSinglePortBridgeGoal P G R)
    (h2 : T.ProductObstructionMultiPortBridgeGoal P G R) :
    T.ProductObstructionToRadicalLargeGoal P G R := by
  intro hinput
  have hsplit : T.ProductObstructionSpecialCaseSplit P G R :=
    T.productObstructionSpecialCaseSplit_of_input P G R hinput
  unfold ProductObstructionSpecialCaseSplit at hsplit
  rcases hsplit with hnone | hone_or_multi
  · exact h0 hnone
  · rcases hone_or_multi with hone | hmulti
    · exact h1 hone
    · exact h2 hmulti

/-- The same special-case bridges also solve the Step 4 named goal. -/
theorem productObstructionStep4Goal_of_specialCaseBridges
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h0 : T.ProductObstructionNoPortBridgeGoal P G R)
    (h1 : T.ProductObstructionSinglePortBridgeGoal P G R)
    (h2 : T.ProductObstructionMultiPortBridgeGoal P G R) :
    T.ProductObstructionStep4Goal P G R := by
  exact T.productObstructionToRadicalLargeGoal_of_specialCaseBridges P G R h0 h1 h2

/-- Step 5 named target: reduce the product-obstruction route to three special
case bridge goals. -/
def ProductObstructionStep5Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionNoPortBridgeGoal P G R ∧
    T.ProductObstructionSinglePortBridgeGoal P G R ∧
      T.ProductObstructionMultiPortBridgeGoal P G R

/-- Step 5 goal supplies the Step 4 radical-large route. -/
theorem productObstructionStep4Goal_of_step5Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionStep5Goal P G R) :
    T.ProductObstructionStep4Goal P G R := by
  exact T.productObstructionStep4Goal_of_specialCaseBridges P G R h.1 h.2.1 h.2.2

end ABCData

end ABD3
