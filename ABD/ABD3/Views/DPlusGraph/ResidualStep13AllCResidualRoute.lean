import ABD.ABD3.Views.DPlusGraph.ResidualStep12GlobalResidualDichotomy

namespace ABD3

namespace ABCData

/-- Step E product-absorption input for the all-C-residual branch.

This is still not the product estimate itself.  It packages exactly the data that
later surplus-absorption/product arguments should consume:

* the Step C pointwise residual ledger is available at every positive C-surplus
  port;
* every positive C-surplus port has C-side residual high against both A and B.

In other words, every positive C-surplus port remains unabsorbed in the directed
C-residual direction. -/
def CSurplusUnabsorbedProductObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CPortPointwiseResidualLedgerAll P G R ∧
    ∀ p, p ∈ T.CSurplusPorts P →
      T.CResidualHighAgainstA P G R p ∧
        T.CResidualHighAgainstB P G R p

/-- The all-C-residual route is exactly the Step E product-obstruction input. -/
theorem cSurplusUnabsorbedProductObstruction_iff_allCResidualRoute
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.CSurplusUnabsorbedProductObstruction P G R ↔
      T.CSurplusAllCResidualRoute P G R := by
  constructor
  · intro h
    unfold CSurplusUnabsorbedProductObstruction at h
    unfold CSurplusAllCResidualRoute CSurplusAllCResidualHighAgainstBoth
    constructor
    · exact h.1
    · intro p hp
      unfold CPortCResidualHighAgainstBoth
      exact h.2 p hp
  · intro h
    unfold CSurplusAllCResidualRoute CSurplusAllCResidualHighAgainstBoth at h
    unfold CSurplusUnabsorbedProductObstruction
    constructor
    · exact h.1
    · intro p hp
      have hpairs : T.CPortCResidualHighAgainstBoth P G R p := h.2 p hp
      unfold CPortCResidualHighAgainstBoth at hpairs
      exact hpairs

/-- Convert the Step D all-C-residual route into the Step E product-obstruction
input. -/
theorem cSurplusUnabsorbedProductObstruction_of_allCResidualRoute
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CSurplusAllCResidualRoute P G R) :
    T.CSurplusUnabsorbedProductObstruction P G R := by
  exact (T.cSurplusUnabsorbedProductObstruction_iff_allCResidualRoute P G R).mpr h

/-- Forget the Step E product-obstruction input back to the all-C-residual route. -/
theorem allCResidualRoute_of_cSurplusUnabsorbedProductObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CSurplusUnabsorbedProductObstruction P G R) :
    T.CSurplusAllCResidualRoute P G R := by
  exact (T.cSurplusUnabsorbedProductObstruction_iff_allCResidualRoute P G R).mp h

/-- The Step E product-obstruction input contains the Step C pointwise ledger. -/
theorem cPortPointwiseResidualLedgerAll_of_productObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CSurplusUnabsorbedProductObstruction P G R) :
    T.CPortPointwiseResidualLedgerAll P G R := by
  exact h.1

/-- The Step E product-obstruction input gives C-residual-high against A at every
positive C-surplus port. -/
theorem cResidualHighAgainstA_of_productObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.CSurplusUnabsorbedProductObstruction P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CResidualHighAgainstA P G R p := by
  exact (h.2 p hp).1

/-- The Step E product-obstruction input gives C-residual-high against B at every
positive C-surplus port. -/
theorem cResidualHighAgainstB_of_productObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.CSurplusUnabsorbedProductObstruction P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CResidualHighAgainstB P G R p := by
  exact (h.2 p hp).2

/-- The Step E product-obstruction input gives the paired C-residual-high fact at
every positive C-surplus port. -/
theorem cPortCResidualHighAgainstBoth_of_productObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.CSurplusUnabsorbedProductObstruction P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortCResidualHighAgainstBoth P G R p := by
  unfold CPortCResidualHighAgainstBoth
  exact h.2 p hp

/-- Under no accepted arithmetic edge, the Step D route split can now be read as:

* either the all-C-residual branch gives the Step E product-obstruction input;
* or we are in the active-residual frontier.

This is the safe Step E replacement for the old informal "mixed case" split. -/
theorem productObstruction_or_activeResidualFrontier_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.CSurplusUnabsorbedProductObstruction P G R ∨
      T.CSurplusActiveResidualFrontier P G R := by
  have hroute : T.CSurplusResidualRouteDichotomy P G R :=
    T.cSurplusResidualRouteDichotomy_of_noAcceptedArithmeticEdge P G R hno
  unfold CSurplusResidualRouteDichotomy at hroute
  rcases hroute with hall | hactive
  · exact Or.inl
      (T.cSurplusUnabsorbedProductObstruction_of_allCResidualRoute P G R hall)
  · exact Or.inr hactive

/-- If no accepted arithmetic edge holds and the active-residual frontier is
absent, then the all-C-residual/product-obstruction branch must occur. -/
theorem productObstruction_of_noAcceptedArithmeticEdge_of_not_activeResidualFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R)
    (hnot : ¬ T.CSurplusActiveResidualFrontier P G R) :
    T.CSurplusUnabsorbedProductObstruction P G R := by
  have hsplit :=
    T.productObstruction_or_activeResidualFrontier_of_noAcceptedArithmeticEdge P G R hno
  rcases hsplit with hprod | hactive
  · exact hprod
  · exfalso
    exact hnot hactive

/-- A named Step E goal: product obstruction is the input expected by the future
surplus-absorption/product contradiction lemma.

The proposition is intentionally an alias for now.  Later files can replace the
right-hand side by an actual product inequality without changing the upstream
Step D interface. -/
def CSurplusAbsorptionProductGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CSurplusUnabsorbedProductObstruction P G R

/-- The product-obstruction input immediately supplies the named Step E product
goal. -/
theorem cSurplusAbsorptionProductGoal_of_productObstruction
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.CSurplusUnabsorbedProductObstruction P G R) :
    T.CSurplusAbsorptionProductGoal P G R := by
  exact h

/-- No accepted arithmetic edge and no active-residual frontier give the named
Step E product goal. -/
theorem cSurplusAbsorptionProductGoal_of_noAcceptedArithmeticEdge_of_not_activeResidualFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R)
    (hnot : ¬ T.CSurplusActiveResidualFrontier P G R) :
    T.CSurplusAbsorptionProductGoal P G R := by
  exact T.cSurplusAbsorptionProductGoal_of_productObstruction P G R
    (T.productObstruction_of_noAcceptedArithmeticEdge_of_not_activeResidualFrontier
      P G R hno hnot)

end ABCData

end ABD3
