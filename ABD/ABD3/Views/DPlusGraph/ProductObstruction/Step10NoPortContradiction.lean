import ABD.ABD3.Views.DPlusGraph.ProductObstruction.Step9MultiPortCase

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 10.

This closes the no-positive-C-surplus-port branch.  If the positive C-surplus port
family is empty, then every positive-surplus exponent on the full ABC support is
zero, hence the positive-surplus product is `1`.  That contradicts the D+ product
dominance forced by `RadicalSmall`. -/
theorem positiveSurplusExpAt_eq_zero_of_noPortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ)
    (hcase : T.ProductObstructionNoPortCase P G R)
    (hpABC : p ∈ T.supportABC) :
    T.PositiveSurplusExpAt P p = 0 := by
  have hEmpty : T.CSurplusPorts P = ∅ :=
    T.cSurplusPorts_eq_empty_of_noPortCase P G R hcase
  have hnotPort : p ∉ T.CSurplusPorts P := by
    rw [hEmpty]
    simp
  have hnotPos : ¬ 0 < T.PositiveSurplusExpAt P p := by
    intro hpos
    have hpPort : p ∈ T.CSurplusPorts P :=
      (T.mem_cSurplusPorts_iff P p).mpr ⟨hpABC, hpos⟩
    exact hnotPort hpPort
  exact Nat.eq_zero_of_not_pos hnotPos

/-- In the no-port case, the positive C-surplus product collapses to `1`. -/
theorem positiveSurplusProduct_eq_one_of_noPortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hcase : T.ProductObstructionNoPortCase P G R) :
    T.PositiveSurplusProduct P = 1 := by
  unfold PositiveSurplusProduct
  apply Finset.prod_eq_one
  intro p hp
  rw [T.positiveSurplusExpAt_eq_zero_of_noPortCase P G R p hcase hp]
  simp

/-- The no-port case contradicts D+ surplus-product dominance. -/
theorem not_surplusProductDominatesDeficit_of_noPortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hcase : T.ProductObstructionNoPortCase P G R) :
    ¬ T.SurplusProductDominatesDeficit P := by
  intro hdom
  unfold SurplusProductDominatesDeficit at hdom
  have hposOne : T.PositiveSurplusProduct P = 1 :=
    T.positiveSurplusProduct_eq_one_of_noPortCase P G R hcase
  have hnegPos : 0 < T.NegativeDeficitProduct P :=
    T.negDeficit_pos P
  have hnegGeOneNat : 1 ≤ T.NegativeDeficitProduct P :=
    Nat.succ_le_of_lt hnegPos
  have hnegGeOneInt : (1 : ℤ) ≤ (T.NegativeDeficitProduct P : ℤ) := by
    exact_mod_cast hnegGeOneNat
  have hltOne : (T.NegativeDeficitProduct P : ℤ) < (1 : ℤ) := by
    simpa [hposOne] using hdom
  exact not_lt_of_ge hnegGeOneInt hltOne

/-- The no-port case contradicts radical-smallness. -/
theorem not_radicalSmall_of_noPortCase
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hcase : T.ProductObstructionNoPortCase P G R) :
    ¬ T.RadicalSmall P := by
  intro hsmall
  have hdom : T.SurplusProductDominatesDeficit P :=
    (T.theoremDPlus_iff P).mp hsmall
  exact (T.not_surplusProductDominatesDeficit_of_noPortCase P G R hcase) hdom

/-- The Step 7 no-port contradiction goal is now proved. -/
theorem productObstructionNoPortContradictionGoal_proved
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.ProductObstructionNoPortContradictionGoal P G R := by
  intro hcase
  exact T.not_radicalSmall_of_noPortCase P G R hcase

/-- A named Step 10 target: the no-port branch is closed. -/
def ProductObstructionStep10Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionNoPortContradictionGoal P G R

/-- Step 10 is available unconditionally from the D+ product dominance theorem. -/
theorem productObstructionStep10Goal_proved
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.ProductObstructionStep10Goal P G R := by
  exact T.productObstructionNoPortContradictionGoal_proved P G R

/-- Step 10 supplies the Step 7 goal. -/
theorem productObstructionStep7Goal_of_step10Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionStep10Goal P G R) :
    T.ProductObstructionStep7Goal P G R := by
  exact h

/-- The Step 7 goal is now proved. -/
theorem productObstructionStep7Goal_proved
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.ProductObstructionStep7Goal P G R := by
  exact T.productObstructionStep7Goal_of_step10Goal P G R
    (T.productObstructionStep10Goal_proved P G R)

/-- With Step 10 closing no-port, the remaining product-obstruction route reduces
to the single-port and multi-port bridges. -/
theorem productObstructionStep5Goal_of_step10Goal_step8BGoal_step9Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h10 : T.ProductObstructionStep10Goal P G R)
    (h8B : T.ProductObstructionStep8BGoal P G R)
    (h9 : T.ProductObstructionStep9Goal P G R) :
    T.ProductObstructionStep5Goal P G R := by
  exact T.productObstructionStep5Goal_of_step7Goal_step8BGoal_step9Goal P G R
    (T.productObstructionStep7Goal_of_step10Goal P G R h10) h8B h9

/-- With Step 10 closing no-port, Step 8B and Step 9 give the Step 4 route. -/
theorem productObstructionStep4Goal_of_step10Goal_step8BGoal_step9Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h10 : T.ProductObstructionStep10Goal P G R)
    (h8B : T.ProductObstructionStep8BGoal P G R)
    (h9 : T.ProductObstructionStep9Goal P G R) :
    T.ProductObstructionStep4Goal P G R := by
  exact T.productObstructionStep4Goal_of_step7Goal_step8BGoal_step9Goal P G R
    (T.productObstructionStep7Goal_of_step10Goal P G R h10) h8B h9

/-- Since Step 10 is proved, the product-obstruction branch now only needs the
single-port and multi-port bridge goals. -/
theorem productObstructionStep4Goal_of_step8BGoal_step9Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h8B : T.ProductObstructionStep8BGoal P G R)
    (h9 : T.ProductObstructionStep9Goal P G R) :
    T.ProductObstructionStep4Goal P G R := by
  exact T.productObstructionStep4Goal_of_step10Goal_step8BGoal_step9Goal P G R
    (T.productObstructionStep10Goal_proved P G R) h8B h9

end ABCData

end ABD3
