import ABD.ABD3.Views.DPlusGraph.ProductObstruction.Step11ASinglePortSurplusNormalForm

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 11B.

This is the logical obstruction layer for the single-port branch.  Once the
positive-surplus product has collapsed to `p ^ s`, it is enough to show that this
same quantity is bounded above by the negative-deficit product; that contradicts
D+ surplus-product dominance and hence radical-smallness. -/
def SinglePortDominanceObstructionAt
    (T : ABCData) (P : PowerData) (p s : ℕ) : Prop :=
  T.PositiveSurplusProduct P = p ^ s ∧
    ((p ^ s : ℕ) : ℤ) ≤ (T.NegativeDeficitProduct P : ℤ)

/-- A single-port surplus normal form can carry the dominance obstruction at its
recorded port and exponent. -/
def ProductObstructionSinglePortDominanceObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ∃ p s,
    T.ProductObstructionSinglePortSurplusNormalFormAt P G R p s ∧
      T.SinglePortDominanceObstructionAt P p s

/-- The single-port dominance obstruction contradicts D+ surplus-product
dominance. -/
theorem not_surplusProductDominatesDeficit_of_singlePortDominanceObstructionAt
    (T : ABCData) (P : PowerData) (p s : ℕ)
    (hobs : T.SinglePortDominanceObstructionAt P p s) :
    ¬ T.SurplusProductDominatesDeficit P := by
  intro hdom
  rcases hobs with ⟨hprod, hle⟩
  unfold SurplusProductDominatesDeficit at hdom
  have hlt : (T.NegativeDeficitProduct P : ℤ) < ((p ^ s : ℕ) : ℤ) := by
    simpa [hprod] using hdom
  exact not_lt_of_ge hle hlt

/-- The existential single-port dominance obstruction contradicts D+ dominance. -/
theorem not_surplusProductDominatesDeficit_of_singlePortDominanceObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hobs : T.ProductObstructionSinglePortDominanceObstruction P G R) :
    ¬ T.SurplusProductDominatesDeficit P := by
  rcases hobs with ⟨p, s, _hsurplus, hpoint⟩
  exact T.not_surplusProductDominatesDeficit_of_singlePortDominanceObstructionAt P p s hpoint

/-- The single-port dominance obstruction contradicts radical-smallness via D+. -/
theorem not_radicalSmall_of_singlePortDominanceObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hobs : T.ProductObstructionSinglePortDominanceObstruction P G R) :
    ¬ T.RadicalSmall P := by
  intro hsmall
  have hdom : T.SurplusProductDominatesDeficit P :=
    (T.theoremDPlus_iff P).mp hsmall
  exact (T.not_surplusProductDominatesDeficit_of_singlePortDominanceObstruction P G R hobs) hdom

/-- The single-port dominance obstruction forces the radical-large side. -/
theorem radicalLarge_of_singlePortDominanceObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hobs : T.ProductObstructionSinglePortDominanceObstruction P G R) :
    T.RadicalLarge P := by
  exact T.radicalLarge_of_not_radicalSmall P
    (T.not_radicalSmall_of_singlePortDominanceObstruction P G R hobs)

/-- The remaining arithmetic goal for the single-port branch: derive the
dominance obstruction from the Step 11A surplus normal form. -/
def ProductObstructionSinglePortDominanceObstructionGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionSinglePortSurplusNormalForm P G R →
    T.ProductObstructionSinglePortDominanceObstruction P G R

/-- A dominance-obstruction goal gives a radical-large bridge from the Step 11A
surplus normal form. -/
def ProductObstructionSinglePortSurplusNormalFormBridgeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionSinglePortSurplusNormalForm P G R → T.RadicalLarge P

/-- The dominance-obstruction goal supplies the Step 11A surplus-normal-form
bridge. -/
theorem singlePortSurplusNormalFormBridgeGoal_of_dominanceObstructionGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.ProductObstructionSinglePortDominanceObstructionGoal P G R) :
    T.ProductObstructionSinglePortSurplusNormalFormBridgeGoal P G R := by
  intro hsurplus
  exact T.radicalLarge_of_singlePortDominanceObstruction P G R (hgoal hsurplus)

/-- A dominance-obstruction goal supplies the Step 8B single-port valuation bridge. -/
theorem productObstructionStep8BGoal_of_dominanceObstructionGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.ProductObstructionSinglePortDominanceObstructionGoal P G R) :
    T.ProductObstructionStep8BGoal P G R := by
  intro hval
  have hsurplus : T.ProductObstructionSinglePortSurplusNormalForm P G R :=
    T.productObstructionSinglePortSurplusNormalForm_of_valuationNormalForm P G R hval
  exact T.radicalLarge_of_singlePortDominanceObstruction P G R (hgoal hsurplus)

/-- Step 11B named target: prove the remaining arithmetic dominance obstruction
for the single-port branch. -/
def ProductObstructionStep11BGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionSinglePortDominanceObstructionGoal P G R

/-- Step 11B supplies the Step 8B single-port bridge. -/
theorem productObstructionStep8BGoal_of_step11BGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionStep11BGoal P G R) :
    T.ProductObstructionStep8BGoal P G R := by
  exact T.productObstructionStep8BGoal_of_dominanceObstructionGoal P G R h

/-- Since no-port is closed by Step 10, Step 11B and the multi-port bridge are
enough for the whole product-obstruction-to-radical-large route. -/
theorem productObstructionStep4Goal_of_step11BGoal_step9Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h11B : T.ProductObstructionStep11BGoal P G R)
    (h9 : T.ProductObstructionStep9Goal P G R) :
    T.ProductObstructionStep4Goal P G R := by
  exact T.productObstructionStep4Goal_of_step8BGoal_step9Goal P G R
    (T.productObstructionStep8BGoal_of_step11BGoal P G R h11B) h9

end ABCData

end ABD3
