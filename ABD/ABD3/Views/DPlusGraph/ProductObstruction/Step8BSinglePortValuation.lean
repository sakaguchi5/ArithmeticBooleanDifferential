import ABD.ABD3.Views.DPlusGraph.ProductObstruction.Step8SinglePortCase
import ABD.ABD3.Views.DPlusGraph.CPortRefinement

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 8B.

The Step 8 singleton port is now expanded into C-valuation language.  This keeps
SinglePort as a one-variable arithmetic problem: a unique positive C-surplus
prime `p`, its C-side reward, its concrete C-port coefficient, and the two
residual lower bounds against the A/B generators. -/
def ProductObstructionSinglePortValuationShape
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ) : Prop :=
  p ∈ T.supportC ∧
    P.N < T.CValuationRewardAt P p ∧
      T.CPortCoeffNat p = T.valC p * (T.C.val / p) ∧
        R + 1 ≤ RightSyncResidualNat G.gA (T.valC p * (T.C.val / p)) ∧
          R + 1 ≤ RightSyncResidualNat G.gB (T.valC p * (T.C.val / p))

/-- The singleton port witness supplies the C-valuation shape. -/
theorem productObstructionSinglePortValuationShape_of_singlePortAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ)
    (h : T.ProductObstructionSinglePortAt P G R p) :
    T.ProductObstructionSinglePortValuationShape P G R p := by
  have hport : p ∈ T.CSurplusPorts P := h.1
  have hval := (T.mem_cSurplusPorts_iff_supportC_and_high_reward P p).mp hport
  rcases hval with ⟨hpC, hreward⟩
  have hcoeff : T.CPortCoeffNat p = T.valC p * (T.C.val / p) :=
    T.cPortCoeffNat_eq_valC_mul_C_div_of_mem_cSurplusPorts P hport
  have hA0 : R + 1 ≤ RightSyncResidualNat G.gA (T.CPortCoeffNat p) :=
    T.singlePortAResidualLowerBound_of_singlePortAt P G R p h
  have hB0 : R + 1 ≤ RightSyncResidualNat G.gB (T.CPortCoeffNat p) :=
    T.singlePortBResidualLowerBound_of_singlePortAt P G R p h
  have hA : R + 1 ≤ RightSyncResidualNat G.gA (T.valC p * (T.C.val / p)) := by
    simpa [hcoeff] using hA0
  have hB : R + 1 ≤ RightSyncResidualNat G.gB (T.valC p * (T.C.val / p)) := by
    simpa [hcoeff] using hB0
  exact ⟨hpC, hreward, hcoeff, hA, hB⟩

/-- Step 8B valuation normal form for the single-port product-obstruction branch.

Compared with Step 8, this version records not just the singleton product shape,
but also the C-side valuation information for the unique port. -/
def ProductObstructionSinglePortValuationNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ∃ p,
    T.ProductObstructionSinglePortAt P G R p ∧
      T.ProductObstructionSinglePortProductShape P G R p ∧
        T.ProductObstructionSinglePortValuationShape P G R p

/-- The Step 8 single-port normal form supplies the Step 8B valuation normal form. -/
theorem productObstructionSinglePortValuationNormalForm_of_singlePortNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionSinglePortNormalForm P G R) :
    T.ProductObstructionSinglePortValuationNormalForm P G R := by
  rcases h with ⟨p, hpAt, hpShape, _hA, _hB⟩
  exact ⟨
    p,
    hpAt,
    hpShape,
    T.productObstructionSinglePortValuationShape_of_singlePortAt P G R p hpAt⟩

/-- A raw single-port case supplies the Step 8B valuation normal form. -/
theorem productObstructionSinglePortValuationNormalForm_of_singlePortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hcase : T.ProductObstructionSinglePortCase P G R) :
    T.ProductObstructionSinglePortValuationNormalForm P G R := by
  exact T.productObstructionSinglePortValuationNormalForm_of_singlePortNormalForm P G R
    (T.productObstructionSinglePortNormalForm_of_singlePortCase P G R hcase)

/-- Forget the Step 8B valuation normal form back to the Step 8 single-port normal
form. -/
theorem productObstructionSinglePortNormalForm_of_valuationNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionSinglePortValuationNormalForm P G R) :
    T.ProductObstructionSinglePortNormalForm P G R := by
  rcases h with ⟨p, hpAt, hpShape, hpVal⟩
  exact ⟨p, hpAt, hpShape, hpVal.2.2.2.1, hpVal.2.2.2.2⟩

/-- Single-port bridge target after C-valuation normalization. -/
def ProductObstructionSinglePortValuationNormalFormBridgeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionSinglePortValuationNormalForm P G R → T.RadicalLarge P

/-- A valuation-normal-form bridge supplies the Step 8 single-port normal-form
bridge. -/
theorem productObstructionSinglePortNormalFormBridgeGoal_of_valuationBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hbridge : T.ProductObstructionSinglePortValuationNormalFormBridgeGoal P G R) :
    T.ProductObstructionSinglePortNormalFormBridgeGoal P G R := by
  intro hnf
  exact hbridge
    (T.productObstructionSinglePortValuationNormalForm_of_singlePortNormalForm P G R hnf)

/-- A valuation-normal-form bridge supplies the single-port bridge required by
Step 5. -/
theorem productObstructionSinglePortBridgeGoal_of_singlePortValuationBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hbridge : T.ProductObstructionSinglePortValuationNormalFormBridgeGoal P G R) :
    T.ProductObstructionSinglePortBridgeGoal P G R := by
  exact T.productObstructionSinglePortBridgeGoal_of_singlePortNormalFormBridge P G R
    (T.productObstructionSinglePortNormalFormBridgeGoal_of_valuationBridge P G R hbridge)

/-- A named Step 8B target: prove the radical-large bridge for the C-valuation
normal form of the single-port branch. -/
def ProductObstructionStep8BGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionSinglePortValuationNormalFormBridgeGoal P G R

/-- Step 8B supplies the Step 8 goal. -/
theorem productObstructionStep8Goal_of_step8BGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionStep8BGoal P G R) :
    T.ProductObstructionStep8Goal P G R := by
  exact T.productObstructionSinglePortNormalFormBridgeGoal_of_valuationBridge P G R h

/-- Step 8B supplies the single-port bridge required by Step 5. -/
theorem productObstructionSinglePortBridgeGoal_of_step8BGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionStep8BGoal P G R) :
    T.ProductObstructionSinglePortBridgeGoal P G R := by
  exact T.productObstructionSinglePortBridgeGoal_of_singlePortValuationBridge P G R h

/-- Step 7, Step 8B, and the remaining multi-port bridge supply the Step 5
special-case package. -/
theorem productObstructionStep5Goal_of_step7Goal_step8BGoal_and_multiBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h7 : T.ProductObstructionStep7Goal P G R)
    (h8B : T.ProductObstructionStep8BGoal P G R)
    (hMulti : T.ProductObstructionMultiPortBridgeGoal P G R) :
    T.ProductObstructionStep5Goal P G R := by
  exact T.productObstructionStep5Goal_of_step7Goal_step8Goal_and_multiBridge P G R
    h7
    (T.productObstructionStep8Goal_of_step8BGoal P G R h8B)
    hMulti

/-- Step 7, Step 8B, and the remaining multi-port bridge already give the Step 4
product-obstruction-to-radical-large route. -/
theorem productObstructionStep4Goal_of_step7Goal_step8BGoal_and_multiBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h7 : T.ProductObstructionStep7Goal P G R)
    (h8B : T.ProductObstructionStep8BGoal P G R)
    (hMulti : T.ProductObstructionMultiPortBridgeGoal P G R) :
    T.ProductObstructionStep4Goal P G R := by
  exact T.productObstructionStep4Goal_of_step5Goal P G R
    (T.productObstructionStep5Goal_of_step7Goal_step8BGoal_and_multiBridge P G R
      h7 h8B hMulti)

/-- The single-port valuation bridge excludes concrete danger on the single-port
branch. -/
def ProductObstructionSinglePortValuationExcludesConcreteDangerGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionSinglePortCase P G R → ¬ T.ConcreteDangerNormalForm P

/-- A single-port valuation-normal-form bridge excludes concrete danger on the
single-port branch. -/
theorem productObstructionSinglePortValuationExcludesConcreteDangerGoal_of_valuationBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hbridge : T.ProductObstructionSinglePortValuationNormalFormBridgeGoal P G R) :
    T.ProductObstructionSinglePortValuationExcludesConcreteDangerGoal P G R := by
  intro hcase hdanger
  have hlarge : T.RadicalLarge P :=
    hbridge (T.productObstructionSinglePortValuationNormalForm_of_singlePortCase P G R hcase)
  have hnsmall : ¬ T.RadicalSmall P :=
    T.not_radicalSmall_of_radicalLarge P hlarge
  exact hnsmall hdanger.1

end ABCData

end ABD3
