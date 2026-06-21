import ABD.ABD3.Views.DPlusGraph.ProductObstruction.Step11BSinglePortDominanceObstruction

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 11C.

This isolates the remaining arithmetic input for the single-port branch.  Step
11A collapsed the positive-surplus product to `p ^ s`, and Step 11B showed that
`p ^ s ≤ NegativeDeficitProduct` contradicts D+ dominance.  This file extracts
the residual lower bounds already present in the single-port surplus normal form
and names the exact remaining goal: those residual bounds must force the
single-port dominance obstruction. -/
def SinglePortResidualLowerBoundsAt
    (T : ABCData)
    (G : ArithmeticSyncGenerators) (R p : ℕ) : Prop :=
  R + 1 ≤ RightSyncResidualNat G.gA (T.valC p * (T.C.val / p)) ∧
    R + 1 ≤ RightSyncResidualNat G.gB (T.valC p * (T.C.val / p))

/-- The residual lower bounds are already contained in the Step 11A single-port
surplus normal form, through its Step 8B valuation shape component. -/
theorem singlePortResidualLowerBoundsAt_of_surplusNormalFormAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p s : ℕ)
    (h : T.ProductObstructionSinglePortSurplusNormalFormAt P G R p s) :
    T.SinglePortResidualLowerBoundsAt G R p := by
  rcases h with ⟨_hpAt, _hpShape, hpVal, _hsEq, _hsPos, _hprod⟩
  exact ⟨hpVal.2.2.2.1, hpVal.2.2.2.2⟩

/-- Step 11C data at the unique single port: the Step 11A surplus normal form
together with the explicitly extracted residual lower bounds. -/
def ProductObstructionSinglePortResidualDataAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p s : ℕ) : Prop :=
  T.ProductObstructionSinglePortSurplusNormalFormAt P G R p s ∧
    T.SinglePortResidualLowerBoundsAt G R p

/-- Build the Step 11C residual data from the Step 11A surplus normal form. -/
theorem singlePortResidualDataAt_of_surplusNormalFormAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p s : ℕ)
    (h : T.ProductObstructionSinglePortSurplusNormalFormAt P G R p s) :
    T.ProductObstructionSinglePortResidualDataAt P G R p s := by
  exact ⟨h, T.singlePortResidualLowerBoundsAt_of_surplusNormalFormAt P G R p s h⟩

/-- Forget the Step 11C residual data back to the Step 11A surplus normal form. -/
theorem surplusNormalFormAt_of_singlePortResidualDataAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p s : ℕ)
    (h : T.ProductObstructionSinglePortResidualDataAt P G R p s) :
    T.ProductObstructionSinglePortSurplusNormalFormAt P G R p s := by
  exact h.1

/-- Extract the residual lower bounds from Step 11C residual data. -/
theorem residualLowerBoundsAt_of_singlePortResidualDataAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p s : ℕ)
    (h : T.ProductObstructionSinglePortResidualDataAt P G R p s) :
    T.SinglePortResidualLowerBoundsAt G R p := by
  exact h.2

/-- The remaining arithmetic goal for the single-port branch.

Given the Step 11C residual data at the unique port, the residual lower bounds
should force the dominance obstruction `p ^ s ≤ NegativeDeficitProduct`.  This is
kept as a goal predicate: proving it is the genuine single-port arithmetic
subproblem. -/
def SinglePortResidualForcesDominanceObstructionGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ∀ p s,
    T.ProductObstructionSinglePortResidualDataAt P G R p s →
      T.SinglePortDominanceObstructionAt P p s

/-- A residual-forces-obstruction goal supplies the Step 11B dominance-obstruction
goal for the single-port branch. -/
theorem singlePortDominanceObstructionGoal_of_residualForcesGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.SinglePortResidualForcesDominanceObstructionGoal P G R) :
    T.ProductObstructionSinglePortDominanceObstructionGoal P G R := by
  intro hsurplus
  rcases hsurplus with ⟨p, s, hs⟩
  have hdata : T.ProductObstructionSinglePortResidualDataAt P G R p s :=
    T.singlePortResidualDataAt_of_surplusNormalFormAt P G R p s hs
  exact ⟨p, s, hs, hgoal p s hdata⟩

/-- A named Step 11C target: residual lower bounds force the single-port dominance
obstruction. -/
def ProductObstructionStep11CGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.SinglePortResidualForcesDominanceObstructionGoal P G R

/-- Step 11C supplies the Step 11B goal. -/
theorem productObstructionStep11BGoal_of_step11CGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionStep11CGoal P G R) :
    T.ProductObstructionStep11BGoal P G R := by
  exact T.singlePortDominanceObstructionGoal_of_residualForcesGoal P G R h

/-- Step 11C supplies the Step 8B single-port bridge. -/
theorem productObstructionStep8BGoal_of_step11CGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionStep11CGoal P G R) :
    T.ProductObstructionStep8BGoal P G R := by
  exact T.productObstructionStep8BGoal_of_step11BGoal P G R
    (T.productObstructionStep11BGoal_of_step11CGoal P G R h)

/-- Since no-port is closed by Step 10, Step 11C and the multi-port bridge are
enough for the whole product-obstruction-to-radical-large route. -/
theorem productObstructionStep4Goal_of_step11CGoal_step9Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h11C : T.ProductObstructionStep11CGoal P G R)
    (h9 : T.ProductObstructionStep9Goal P G R) :
    T.ProductObstructionStep4Goal P G R := by
  exact T.productObstructionStep4Goal_of_step11BGoal_step9Goal P G R
    (T.productObstructionStep11BGoal_of_step11CGoal P G R h11C) h9

end ABCData

end ABD3
