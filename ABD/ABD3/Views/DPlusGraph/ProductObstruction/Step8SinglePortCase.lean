import ABD.ABD3.Views.DPlusGraph.ProductObstruction.Step7NoPortCase

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 8.

The exactly-one-positive-C-surplus-port case.  This file does not try to prove
that the single-port branch forces `RadicalLarge`; instead it normalizes the
branch to a one-port residual/product shape and isolates the bridge goal that
remains. -/
def ProductObstructionSinglePortAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ) : Prop :=
  p ∈ T.CSurplusPorts P ∧
    T.CSurplusPorts P = {p} ∧
      T.ProductObstructionInput P G R

/-- A single-port case contains a unique recorded C-surplus port. -/
theorem exists_singlePortAt_of_singlePortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hcase : T.ProductObstructionSinglePortCase P G R) :
    ∃ p, T.ProductObstructionSinglePortAt P G R p := by
  obtain ⟨p, hset⟩ := Finset.card_eq_one.mp hcase.1
  refine ⟨p, ?_⟩
  unfold ProductObstructionSinglePortAt
  exact ⟨by rw [hset]; simp, hset, hcase.2⟩

/-- Forget a single-port-at witness back to the local product-obstruction input. -/
theorem productObstructionInput_of_singlePortAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ)
    (h : T.ProductObstructionSinglePortAt P G R p) :
    T.ProductObstructionInput P G R := by
  exact h.2.2

/-- In a one-port branch, the baseline product is the single factor `R + 1`. -/
theorem cResidualBaselineProduct_eq_of_singlePortAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ)
    (h : T.ProductObstructionSinglePortAt P G R p) :
    T.CResidualBaselineProduct P R = R + 1 := by
  unfold CResidualBaselineProduct
  rw [h.2.1]
  simp

/-- In a one-port branch, the A-facing residual product is the single A-facing
residual factor. -/
theorem cResidualProductAgainstA_eq_of_singlePortAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ)
    (h : T.ProductObstructionSinglePortAt P G R p) :
    T.CResidualProductAgainstA P G =
      RightSyncResidualNat G.gA (T.CPortCoeffNat p) := by
  unfold CResidualProductAgainstA
  rw [h.2.1]
  simp

/-- In a one-port branch, the B-facing residual product is the single B-facing
residual factor. -/
theorem cResidualProductAgainstB_eq_of_singlePortAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ)
    (h : T.ProductObstructionSinglePortAt P G R p) :
    T.CResidualProductAgainstB P G =
      RightSyncResidualNat G.gB (T.CPortCoeffNat p) := by
  unfold CResidualProductAgainstB
  rw [h.2.1]
  simp

/-- The A-facing residual at the unique port is at least `R + 1`. -/
theorem singlePortAResidualLowerBound_of_singlePortAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ)
    (h : T.ProductObstructionSinglePortAt P G R p) :
    R + 1 ≤ RightSyncResidualNat G.gA (T.CPortCoeffNat p) := by
  exact
    (T.cResidualProductLowerBoundAgainstA_of_productObstructionInput P G R h.2.2)
      p h.1

/-- The B-facing residual at the unique port is at least `R + 1`. -/
theorem singlePortBResidualLowerBound_of_singlePortAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ)
    (h : T.ProductObstructionSinglePortAt P G R p) :
    R + 1 ≤ RightSyncResidualNat G.gB (T.CPortCoeffNat p) := by
  exact
    (T.cResidualProductLowerBoundAgainstB_of_productObstructionInput P G R h.2.2)
      p h.1

/-- One-port product shape: all C-residual products collapse to the single
recorded C-surplus port. -/
def ProductObstructionSinglePortProductShape
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ) : Prop :=
  T.CSurplusPorts P = {p} ∧
    T.CResidualBaselineProduct P R = R + 1 ∧
      T.CResidualProductAgainstA P G =
        RightSyncResidualNat G.gA (T.CPortCoeffNat p) ∧
        T.CResidualProductAgainstB P G =
          RightSyncResidualNat G.gB (T.CPortCoeffNat p)

/-- The one-port-at witness supplies its product shape. -/
theorem productObstructionSinglePortProductShape_of_singlePortAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ)
    (h : T.ProductObstructionSinglePortAt P G R p) :
    T.ProductObstructionSinglePortProductShape P G R p := by
  exact ⟨
    h.2.1,
    T.cResidualBaselineProduct_eq_of_singlePortAt P G R p h,
    T.cResidualProductAgainstA_eq_of_singlePortAt P G R p h,
    T.cResidualProductAgainstB_eq_of_singlePortAt P G R p h⟩

/-- One-port normal form for the product-obstruction branch.

This packages the unique port, the singleton product shape, and both residual
lower bounds at that port. -/
def ProductObstructionSinglePortNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ∃ p,
    T.ProductObstructionSinglePortAt P G R p ∧
      T.ProductObstructionSinglePortProductShape P G R p ∧
        R + 1 ≤ RightSyncResidualNat G.gA (T.CPortCoeffNat p) ∧
          R + 1 ≤ RightSyncResidualNat G.gB (T.CPortCoeffNat p)

/-- The raw single-port case supplies the Step 8 one-port normal form. -/
theorem productObstructionSinglePortNormalForm_of_singlePortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hcase : T.ProductObstructionSinglePortCase P G R) :
    T.ProductObstructionSinglePortNormalForm P G R := by
  obtain ⟨p, hp⟩ := T.exists_singlePortAt_of_singlePortCase P G R hcase
  exact ⟨
    p,
    hp,
    T.productObstructionSinglePortProductShape_of_singlePortAt P G R p hp,
    T.singlePortAResidualLowerBound_of_singlePortAt P G R p hp,
    T.singlePortBResidualLowerBound_of_singlePortAt P G R p hp⟩

/-- Single-port bridge target after Step 8 normalization. -/
def ProductObstructionSinglePortNormalFormBridgeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionSinglePortNormalForm P G R → T.RadicalLarge P

/-- A normal-form bridge supplies the single-port bridge required by Step 5. -/
theorem productObstructionSinglePortBridgeGoal_of_singlePortNormalFormBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hbridge : T.ProductObstructionSinglePortNormalFormBridgeGoal P G R) :
    T.ProductObstructionSinglePortBridgeGoal P G R := by
  intro hcase
  exact hbridge (T.productObstructionSinglePortNormalForm_of_singlePortCase P G R hcase)

/-- A named Step 8 target: prove the radical-large bridge for the normalized
single-port branch. -/
def ProductObstructionStep8Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionSinglePortNormalFormBridgeGoal P G R

/-- Step 8 supplies the single-port bridge required by Step 5. -/
theorem productObstructionSinglePortBridgeGoal_of_step8Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionStep8Goal P G R) :
    T.ProductObstructionSinglePortBridgeGoal P G R := by
  exact T.productObstructionSinglePortBridgeGoal_of_singlePortNormalFormBridge P G R h

/-- Step 7, Step 8, and the remaining multi-port bridge supply the Step 5 package. -/
theorem productObstructionStep5Goal_of_step7Goal_step8Goal_and_multiBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h7 : T.ProductObstructionStep7Goal P G R)
    (h8 : T.ProductObstructionStep8Goal P G R)
    (hMulti : T.ProductObstructionMultiPortBridgeGoal P G R) :
    T.ProductObstructionStep5Goal P G R := by
  exact T.productObstructionStep5Goal_of_step7Goal_and_remainingBridges P G R
    h7
    (T.productObstructionSinglePortBridgeGoal_of_step8Goal P G R h8)
    hMulti

/-- Step 7, Step 8, and the remaining multi-port bridge already give the Step 4
product-obstruction-to-radical-large route. -/
theorem productObstructionStep4Goal_of_step7Goal_step8Goal_and_multiBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h7 : T.ProductObstructionStep7Goal P G R)
    (h8 : T.ProductObstructionStep8Goal P G R)
    (hMulti : T.ProductObstructionMultiPortBridgeGoal P G R) :
    T.ProductObstructionStep4Goal P G R := by
  exact T.productObstructionStep4Goal_of_step5Goal P G R
    (T.productObstructionStep5Goal_of_step7Goal_step8Goal_and_multiBridge P G R
      h7 h8 hMulti)

/-- The single-port normalized bridge also excludes concrete danger on the
single-port branch. -/
def ProductObstructionSinglePortExcludesConcreteDangerGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionSinglePortCase P G R → ¬ T.ConcreteDangerNormalForm P

/-- A single-port normal-form bridge excludes concrete danger on the single-port
branch. -/
theorem productObstructionSinglePortExcludesConcreteDangerGoal_of_singlePortNormalFormBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hbridge : T.ProductObstructionSinglePortNormalFormBridgeGoal P G R) :
    T.ProductObstructionSinglePortExcludesConcreteDangerGoal P G R := by
  intro hcase hdanger
  have hlarge : T.RadicalLarge P :=
    hbridge (T.productObstructionSinglePortNormalForm_of_singlePortCase P G R hcase)
  have hnsmall : ¬ T.RadicalSmall P :=
    T.not_radicalSmall_of_radicalLarge P hlarge
  exact hnsmall hdanger.1

end ABCData

end ABD3
