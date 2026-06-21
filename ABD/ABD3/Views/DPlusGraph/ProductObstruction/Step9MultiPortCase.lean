import ABD.ABD3.Views.DPlusGraph.ProductObstruction.Step8BSinglePortValuation

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 9.

The multi-positive-C-surplus-port branch is normalized pointwise in C-valuation
language.  This is the multi-port analogue of Step 8B: every recorded port is a
C-side support prime, has C-reward above the radical tax, has the concrete C-port
coefficient `valC p * (C / p)`, and carries both A/B residual lower bounds. -/
def ProductObstructionMultiPortValuationShapeAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ) : Prop :=
  p ∈ T.CSurplusPorts P ∧
    p ∈ T.supportC ∧
      P.N < T.CValuationRewardAt P p ∧
        T.CPortCoeffNat p = T.valC p * (T.C.val / p) ∧
          R + 1 ≤ RightSyncResidualNat G.gA (T.valC p * (T.C.val / p)) ∧
            R + 1 ≤ RightSyncResidualNat G.gB (T.valC p * (T.C.val / p))

/-- A recorded C-surplus port in a product-obstruction input supplies its
C-valuation/residual shape. -/
theorem productObstructionMultiPortValuationShapeAt_of_mem_cSurplusPorts
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ)
    (hinput : T.ProductObstructionInput P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.ProductObstructionMultiPortValuationShapeAt P G R p := by
  have hval := (T.mem_cSurplusPorts_iff_supportC_and_high_reward P p).mp hp
  rcases hval with ⟨hpC, hreward⟩
  have hcoeff : T.CPortCoeffNat p = T.valC p * (T.C.val / p) :=
    T.cPortCoeffNat_eq_valC_mul_C_div_of_mem_cSurplusPorts P hp
  have hA0 : R + 1 ≤ RightSyncResidualNat G.gA (T.CPortCoeffNat p) :=
    (T.cResidualProductLowerBoundAgainstA_of_productObstructionInput P G R hinput) p hp
  have hB0 : R + 1 ≤ RightSyncResidualNat G.gB (T.CPortCoeffNat p) :=
    (T.cResidualProductLowerBoundAgainstB_of_productObstructionInput P G R hinput) p hp
  have hA : R + 1 ≤ RightSyncResidualNat G.gA (T.valC p * (T.C.val / p)) := by
    simpa [hcoeff] using hA0
  have hB : R + 1 ≤ RightSyncResidualNat G.gB (T.valC p * (T.C.val / p)) := by
    simpa [hcoeff] using hB0
  exact ⟨hp, hpC, hreward, hcoeff, hA, hB⟩

/-- Multi-port valuation normal form for the product-obstruction branch.

Compared with the raw Step 5 multi-port case, this records:
* at least two positive C-surplus ports;
* the original product-obstruction input;
* the literal Step 6 finite-product lower-bound ledger;
* the C-valuation/residual shape at every recorded port. -/
def ProductObstructionMultiPortValuationNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  2 ≤ (T.CSurplusPorts P).card ∧
    T.ProductObstructionInput P G R ∧
      T.CResidualLiteralProductLowerBound P G R ∧
        ∀ p, p ∈ T.CSurplusPorts P →
          T.ProductObstructionMultiPortValuationShapeAt P G R p

/-- A raw multi-port case supplies the Step 9 valuation/product normal form. -/
theorem productObstructionMultiPortValuationNormalForm_of_multiPortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hcase : T.ProductObstructionMultiPortCase P G R) :
    T.ProductObstructionMultiPortValuationNormalForm P G R := by
  have hinput : T.ProductObstructionInput P G R := hcase.2
  exact ⟨
    hcase.1,
    hinput,
    T.cResidualLiteralProductLowerBound_of_productObstructionInput P G R hinput,
    fun p hp =>
      T.productObstructionMultiPortValuationShapeAt_of_mem_cSurplusPorts P G R p hinput hp⟩

/-- Forget the Step 9 normal form back to the local product-obstruction input. -/
theorem productObstructionInput_of_multiPortValuationNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionMultiPortValuationNormalForm P G R) :
    T.ProductObstructionInput P G R := by
  exact h.2.1

/-- Extract the literal product lower-bound ledger from the Step 9 normal form. -/
theorem cResidualLiteralProductLowerBound_of_multiPortValuationNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionMultiPortValuationNormalForm P G R) :
    T.CResidualLiteralProductLowerBound P G R := by
  exact h.2.2.1

/-- Extract the pointwise C-valuation shape from the Step 9 normal form. -/
theorem multiPortValuationShapeAt_of_multiPortValuationNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ)
    (h : T.ProductObstructionMultiPortValuationNormalForm P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.ProductObstructionMultiPortValuationShapeAt P G R p := by
  exact h.2.2.2 p hp

/-- Multi-port bridge target after Step 9 normalization. -/
def ProductObstructionMultiPortValuationNormalFormBridgeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionMultiPortValuationNormalForm P G R → T.RadicalLarge P

/-- A valuation-normal-form bridge supplies the multi-port bridge required by
Step 5. -/
theorem productObstructionMultiPortBridgeGoal_of_multiPortValuationBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hbridge : T.ProductObstructionMultiPortValuationNormalFormBridgeGoal P G R) :
    T.ProductObstructionMultiPortBridgeGoal P G R := by
  intro hcase
  exact hbridge (T.productObstructionMultiPortValuationNormalForm_of_multiPortCase P G R hcase)

/-- A named Step 9 target: prove the radical-large bridge for the normalized
multi-port branch. -/
def ProductObstructionStep9Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionMultiPortValuationNormalFormBridgeGoal P G R

/-- Step 9 supplies the multi-port bridge required by Step 5. -/
theorem productObstructionMultiPortBridgeGoal_of_step9Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionStep9Goal P G R) :
    T.ProductObstructionMultiPortBridgeGoal P G R := by
  exact T.productObstructionMultiPortBridgeGoal_of_multiPortValuationBridge P G R h

/-- Step 7, Step 8B, and Step 9 supply the Step 5 special-case package. -/
theorem productObstructionStep5Goal_of_step7Goal_step8BGoal_step9Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h7 : T.ProductObstructionStep7Goal P G R)
    (h8B : T.ProductObstructionStep8BGoal P G R)
    (h9 : T.ProductObstructionStep9Goal P G R) :
    T.ProductObstructionStep5Goal P G R := by
  exact T.productObstructionStep5Goal_of_step7Goal_step8BGoal_and_multiBridge P G R
    h7 h8B (T.productObstructionMultiPortBridgeGoal_of_step9Goal P G R h9)

/-- Step 7, Step 8B, and Step 9 already give the Step 4
product-obstruction-to-radical-large route. -/
theorem productObstructionStep4Goal_of_step7Goal_step8BGoal_step9Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h7 : T.ProductObstructionStep7Goal P G R)
    (h8B : T.ProductObstructionStep8BGoal P G R)
    (h9 : T.ProductObstructionStep9Goal P G R) :
    T.ProductObstructionStep4Goal P G R := by
  exact T.productObstructionStep4Goal_of_step5Goal P G R
    (T.productObstructionStep5Goal_of_step7Goal_step8BGoal_step9Goal P G R h7 h8B h9)

/-- The multi-port valuation bridge excludes concrete danger on the multi-port
branch. -/
def ProductObstructionMultiPortValuationExcludesConcreteDangerGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionMultiPortCase P G R → ¬ T.ConcreteDangerNormalForm P

/-- A multi-port valuation-normal-form bridge excludes concrete danger on the
multi-port branch. -/
theorem productObstructionMultiPortValuationExcludesConcreteDangerGoal_of_valuationBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hbridge : T.ProductObstructionMultiPortValuationNormalFormBridgeGoal P G R) :
    T.ProductObstructionMultiPortValuationExcludesConcreteDangerGoal P G R := by
  intro hcase hdanger
  have hlarge : T.RadicalLarge P :=
    hbridge (T.productObstructionMultiPortValuationNormalForm_of_multiPortCase P G R hcase)
  have hnsmall : ¬ T.RadicalSmall P :=
    T.not_radicalSmall_of_radicalLarge P hlarge
  exact hnsmall hdanger.1

end ABCData

end ABD3
