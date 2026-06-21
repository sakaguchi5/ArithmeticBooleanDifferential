import ABD.ABD3.Views.DPlusGraph.ResidualStep4Dominance

namespace ABD3

namespace ABCData

/-- Step 5 support-small residual frontier.

This is intentionally an alias for the existing graph-exceptional support-small
side.  The residual layer keeps the next contradiction argument local to the
unaccepted C-port mass before sending it back to `DPlusGraphExceptional`. -/
def ResidualSupportSmall
    (T : ABCData) (_P : PowerData)
    (_G : ArithmeticSyncGenerators) (_R : ℕ) : Prop :=
  T.SupportSmallExceptional

/-- Step 5 surplus-isolated residual frontier.

This is intentionally an alias for the existing graph-exceptional
surplus-isolated side.  Later files can refine this into explicit gcd/lcm
isolation conditions for unaccepted C-ports. -/
def ResidualSurplusIsolated
    (T : ABCData) (P : PowerData)
    (_G : ArithmeticSyncGenerators) (_R : ℕ) : Prop :=
  T.SurplusIsolatedExceptional P

/-- Step 5 unit-boundary residual frontier. -/
def ResidualUnitBoundary (T : ABCData) : Prop :=
  T.UnitBoundary

/-- Step 5 residual frontier.

After Steps 1--4, the remaining task is no longer to prove graph-exceptionality
directly from D+ dominance.  It is to show that residual unaccepted C-port
dominance forces one of the concrete frontier patterns below. -/
def ResidualFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ResidualSupportSmall P G R ∨
    T.ResidualSurplusIsolated P G R ∨
      T.ResidualUnitBoundary

/-- Support-small triples are in the residual frontier. -/
theorem residualFrontier_of_supportSmall
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.SupportSmallExceptional) :
    T.ResidualFrontier P G R := by
  unfold ResidualFrontier ResidualSupportSmall
  exact Or.inl h

/-- Surplus-isolated triples are in the residual frontier. -/
theorem residualFrontier_of_surplusIsolated
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.SurplusIsolatedExceptional P) :
    T.ResidualFrontier P G R := by
  unfold ResidualFrontier ResidualSurplusIsolated
  exact Or.inr (Or.inl h)

/-- Unit-boundary triples are in the residual frontier. -/
theorem residualFrontier_of_unitBoundary
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.UnitBoundary) :
    T.ResidualFrontier P G R := by
  unfold ResidualFrontier ResidualUnitBoundary
  exact Or.inr (Or.inr h)

/-- The residual frontier is enough to return to the existing graph-exceptional
side. -/
theorem dPlusGraphExceptional_of_residualFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ResidualFrontier P G R) :
    T.DPlusGraphExceptional P := by
  unfold ResidualFrontier ResidualSupportSmall
    ResidualSurplusIsolated ResidualUnitBoundary at h
  unfold DPlusGraphExceptional
  rcases h with hsupport | hrest
  · exact Or.inr (Or.inl hsupport)
  · rcases hrest with hisolated | hunit
    · exact Or.inr (Or.inr hisolated)
    · exact Or.inl hunit

/-- Conversely, the existing graph-exceptional side can be read as the residual
frontier.  This is useful when older goals have already produced
`DPlusGraphExceptional`. -/
theorem residualFrontier_of_dPlusGraphExceptional
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.DPlusGraphExceptional P) :
    T.ResidualFrontier P G R := by
  unfold DPlusGraphExceptional at h
  rcases h with hunit | hrest
  · exact T.residualFrontier_of_unitBoundary P G R hunit
  · rcases hrest with hsupport | hisolated
    · exact T.residualFrontier_of_supportSmall P G R hsupport
    · exact T.residualFrontier_of_surplusIsolated P G R hisolated

/-- Residual frontier is equivalent to the existing graph-exceptional side.  The
point of Step 5 is not to change the final exceptional class, but to expose the
intermediate residual cases that the next mathematics must analyze. -/
theorem residualFrontier_iff_dPlusGraphExceptional
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.ResidualFrontier P G R ↔ T.DPlusGraphExceptional P := by
  constructor
  · exact T.dPlusGraphExceptional_of_residualFrontier P G R
  · exact T.residualFrontier_of_dPlusGraphExceptional P G R

end ABCData

end ABD3
