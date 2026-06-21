import ABD.ABD3.Core.RadicalSmall
import ABD.ABD3.Views.DPlusGraph.ProductObstruction.Step3UnabsorbedProduct

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 4.

This is the first real target of the route: turn the unabsorbed C-surplus product
ledger into the radical-large side.  It is intentionally a goal predicate, not an
axiom or asserted theorem. -/
def CUnabsorbedProductToRadicalLargeBridgeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CUnabsorbedProductLowerBound P G R → T.RadicalLarge P

/-- The direct ProductObstruction-to-RadicalLarge goal. -/
def ProductObstructionToRadicalLargeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionInput P G R → T.RadicalLarge P

/-- A bridge from unabsorbed-product lower bounds to radical-large is enough to
solve the direct product-obstruction goal. -/
theorem productObstructionToRadicalLargeGoal_of_unabsorbedProductBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hbridge : T.CUnabsorbedProductToRadicalLargeBridgeGoal P G R) :
    T.ProductObstructionToRadicalLargeGoal P G R := by
  intro hinput
  exact hbridge (T.cUnabsorbedProductLowerBound_of_productObstructionInput P G R hinput)

/-- Radical-large contradicts radical-small. -/
theorem not_radicalSmall_of_radicalLarge
    (T : ABCData) (P : PowerData)
    (hlarge : T.RadicalLarge P) :
    ¬ T.RadicalSmall P := by
  intro hsmall
  unfold RadicalLarge at hlarge
  unfold RadicalSmall RadicalSmallInt at hsmall
  exact not_lt_of_ge hlarge hsmall

/-- Product-obstruction exclusion of the concrete dangerous normal form. -/
def ProductObstructionExcludesConcreteDangerGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionInput P G R → ¬ T.ConcreteDangerNormalForm P

/-- The radical-large product goal excludes the concrete dangerous normal form. -/
theorem productObstructionExcludesConcreteDangerGoal_of_radicalLargeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.ProductObstructionToRadicalLargeGoal P G R) :
    T.ProductObstructionExcludesConcreteDangerGoal P G R := by
  intro hinput hdanger
  have hlarge : T.RadicalLarge P := hgoal hinput
  have hnsmall : ¬ T.RadicalSmall P :=
    T.not_radicalSmall_of_radicalLarge P hlarge
  exact hnsmall hdanger.1

/-- Step 4 named target: the product-obstruction branch should force radical-large.

Later files should prove this by supplying
`CUnabsorbedProductToRadicalLargeBridgeGoal`. -/
def ProductObstructionStep4Goal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionToRadicalLargeGoal P G R

/-- The unabsorbed-product bridge supplies the named Step 4 goal. -/
theorem productObstructionStep4Goal_of_unabsorbedProductBridge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hbridge : T.CUnabsorbedProductToRadicalLargeBridgeGoal P G R) :
    T.ProductObstructionStep4Goal P G R := by
  exact T.productObstructionToRadicalLargeGoal_of_unabsorbedProductBridge P G R hbridge

end ABCData

end ABD3
