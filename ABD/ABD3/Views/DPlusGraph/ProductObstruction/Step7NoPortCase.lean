import ABD.ABD3.Views.DPlusGraph.ProductObstruction.Step6ProductLowerBound

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 7.

The no-positive-C-surplus-port boundary case.  This file does not assert the hard
mathematical fact that the no-port case is impossible in the dangerous regime.
Instead, it isolates the exact contradiction/bridge goal needed for the no-port
branch and connects it back to the Step 5/Step 6 product-obstruction route. -/
def ProductObstructionNoPortContradictionGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionNoPortCase P G R → ¬ T.RadicalSmall P

/-- Negating radical-small is equivalent to the radical-large side for the
integer-power normal form used in ABD3. -/
theorem radicalLarge_of_not_radicalSmall
    (T : ABCData) (P : PowerData)
    (h : ¬ T.RadicalSmall P) :
    T.RadicalLarge P := by
  unfold RadicalSmall RadicalSmallInt at h
  unfold RadicalLarge
  exact le_of_not_gt h

/-- A no-port contradiction against radical-small supplies the no-port bridge used
by Step 5. -/
theorem productObstructionNoPortBridgeGoal_of_noPortContradictionGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.ProductObstructionNoPortContradictionGoal P G R) :
    T.ProductObstructionNoPortBridgeGoal P G R := by
  intro hcase
  exact T.radicalLarge_of_not_radicalSmall P (hgoal hcase)

/-- In the no-port case, the positive C-surplus port family is empty. -/
theorem cSurplusPorts_eq_empty_of_noPortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hcase : T.ProductObstructionNoPortCase P G R) :
    T.CSurplusPorts P = ∅ := by
  exact Finset.card_eq_zero.mp hcase.1

/-- In the no-port case, the baseline residual product is `1`. -/
theorem cResidualBaselineProduct_eq_one_of_noPortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hcase : T.ProductObstructionNoPortCase P G R) :
    T.CResidualBaselineProduct P R = 1 := by
  unfold CResidualBaselineProduct
  rw [T.cSurplusPorts_eq_empty_of_noPortCase P G R hcase]
  simp

/-- In the no-port case, the A-facing residual product is `1`. -/
theorem cResidualProductAgainstA_eq_one_of_noPortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hcase : T.ProductObstructionNoPortCase P G R) :
    T.CResidualProductAgainstA P G = 1 := by
  unfold CResidualProductAgainstA
  rw [T.cSurplusPorts_eq_empty_of_noPortCase P G R hcase]
  simp

/-- In the no-port case, the B-facing residual product is `1`. -/
theorem cResidualProductAgainstB_eq_one_of_noPortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hcase : T.ProductObstructionNoPortCase P G R) :
    T.CResidualProductAgainstB P G = 1 := by
  unfold CResidualProductAgainstB
  rw [T.cSurplusPorts_eq_empty_of_noPortCase P G R hcase]
  simp

/-- Shape information carried by the no-port branch: all residual products over
positive C-surplus ports collapse to the empty product. -/
def ProductObstructionNoPortProductShape
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CResidualBaselineProduct P R = 1 ∧
    T.CResidualProductAgainstA P G = 1 ∧
      T.CResidualProductAgainstB P G = 1

/-- The no-port case supplies its empty-product shape. -/
theorem productObstructionNoPortProductShape_of_noPortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hcase : T.ProductObstructionNoPortCase P G R) :
    T.ProductObstructionNoPortProductShape P G R := by
  exact ⟨
    T.cResidualBaselineProduct_eq_one_of_noPortCase P G R hcase,
    T.cResidualProductAgainstA_eq_one_of_noPortCase P G R hcase,
    T.cResidualProductAgainstB_eq_one_of_noPortCase P G R hcase⟩

/-- The no-port case still carries the literal Step 6 product witness, but the
products are now empty products. -/
def ProductObstructionNoPortLiteralProductWitness
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionNoPortCase P G R ∧
    T.CResidualLiteralProductWitness P G R ∧
      T.ProductObstructionNoPortProductShape P G R

/-- Build the no-port literal-product witness from the no-port case. -/
theorem productObstructionNoPortLiteralProductWitness_of_noPortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hcase : T.ProductObstructionNoPortCase P G R) :
    T.ProductObstructionNoPortLiteralProductWitness P G R := by
  have hinput : T.ProductObstructionInput P G R := hcase.2
  exact ⟨
    hcase,
    T.cResidualLiteralProductWitness_of_productObstructionInput P G R hinput,
    T.productObstructionNoPortProductShape_of_noPortCase P G R hcase⟩

/-- A named Step 7 target: prove that the no-port branch contradicts the
radical-small side.  Once this is proved, the no-port bridge required by Step 5 is
available automatically. -/
def ProductObstructionStep7Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionNoPortContradictionGoal P G R

/-- Step 7 supplies the no-port bridge required by Step 5. -/
theorem productObstructionNoPortBridgeGoal_of_step7Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionStep7Goal P G R) :
    T.ProductObstructionNoPortBridgeGoal P G R := by
  exact T.productObstructionNoPortBridgeGoal_of_noPortContradictionGoal P G R h

/-- Step 7 plus the remaining one-port and multi-port bridges supplies the Step 5
special-case package. -/
theorem productObstructionStep5Goal_of_step7Goal_and_remainingBridges
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h7 : T.ProductObstructionStep7Goal P G R)
    (hSingle : T.ProductObstructionSinglePortBridgeGoal P G R)
    (hMulti : T.ProductObstructionMultiPortBridgeGoal P G R) :
    T.ProductObstructionStep5Goal P G R := by
  exact ⟨
    T.productObstructionNoPortBridgeGoal_of_step7Goal P G R h7,
    hSingle,
    hMulti⟩

/-- Step 7 plus the remaining one-port and multi-port bridges already gives the
Step 4 product-obstruction-to-radical-large route. -/
theorem productObstructionStep4Goal_of_step7Goal_and_remainingBridges
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h7 : T.ProductObstructionStep7Goal P G R)
    (hSingle : T.ProductObstructionSinglePortBridgeGoal P G R)
    (hMulti : T.ProductObstructionMultiPortBridgeGoal P G R) :
    T.ProductObstructionStep4Goal P G R := by
  exact T.productObstructionStep4Goal_of_step5Goal P G R
    (T.productObstructionStep5Goal_of_step7Goal_and_remainingBridges P G R
      h7 hSingle hMulti)

/-- The no-port contradiction goal also excludes concrete danger on the no-port
branch. -/
def ProductObstructionNoPortExcludesConcreteDangerGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionNoPortCase P G R → ¬ T.ConcreteDangerNormalForm P

/-- A no-port radical-small contradiction excludes concrete danger. -/
theorem productObstructionNoPortExcludesConcreteDangerGoal_of_noPortContradictionGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.ProductObstructionNoPortContradictionGoal P G R) :
    T.ProductObstructionNoPortExcludesConcreteDangerGoal P G R := by
  intro hcase hdanger
  exact (hgoal hcase) hdanger.1

end ABCData

end ABD3
