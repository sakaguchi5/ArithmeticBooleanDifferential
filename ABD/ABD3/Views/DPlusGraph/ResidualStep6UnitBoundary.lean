import ABD.ABD3.Views.DPlusGraph.ResidualStep5Frontier

namespace ABD3

namespace ABCData

/-- Step 6 goal: unit-boundary triples immediately fall to graph-exceptional.

This isolates the easy part of the residual frontier.  The remaining hard parts
are support-small and surplus-isolated. -/
def UnitBoundaryForcesGraphExceptionalGoal
    (T : ABCData) (P : PowerData) : Prop :=
  T.UnitBoundary → T.DPlusGraphExceptional P

/-- Step 6: unit boundary is one of the disjuncts of `DPlusGraphExceptional`. -/
theorem unitBoundaryForcesGraphExceptionalGoal
    (T : ABCData) (P : PowerData) :
    T.UnitBoundaryForcesGraphExceptionalGoal P := by
  intro hunit
  unfold DPlusGraphExceptional
  exact Or.inl hunit

/-- Direct Step 6 theorem form. -/
theorem dPlusGraphExceptional_of_unitBoundary
    (T : ABCData) (P : PowerData)
    (hunit : T.UnitBoundary) :
    T.DPlusGraphExceptional P := by
  exact T.unitBoundaryForcesGraphExceptionalGoal P hunit

/-- Unit-boundary triples are already in the residual frontier. -/
theorem step6_residualFrontier_of_unitBoundary
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hunit : T.UnitBoundary) :
    T.ResidualFrontier P G R := by
  exact T.residualFrontier_of_unitBoundary P G R hunit

/-- If a triple is unit-boundary, then the Step 5 frontier goal is automatic:
any residual dominance hypothesis lands in the unit-boundary frontier. -/
theorem residualUnacceptedDominanceForcesFrontierGoal_of_unitBoundary
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hunit : T.UnitBoundary) :
    T.ResidualUnacceptedDominanceForcesFrontierGoal P G R := by
  intro _hresidual
  exact T.step6_residualFrontier_of_unitBoundary P G R hunit

/-- If a triple is unit-boundary, then the Step 4 graph-exceptional residual goal
is automatic. -/
theorem residualUnacceptedDominanceForcesGraphExceptionalGoal_of_unitBoundary
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hunit : T.UnitBoundary) :
    T.ResidualUnacceptedDominanceForcesGraphExceptionalGoal P G R := by
  intro _hresidual
  exact T.dPlusGraphExceptional_of_unitBoundary P hunit

/-- Unit-boundary triples satisfy the low-absorption contradiction goal. -/
theorem dPlusLowAbsorptionContradictionGoal_of_unitBoundary
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hunit : T.UnitBoundary) :
    T.DPlusLowAbsorptionContradictionGoal P G R := by
  exact T.dPlusLowAbsorptionContradictionGoal_of_residualFrontierGoal
    P G R
    (T.residualUnacceptedDominanceForcesFrontierGoal_of_unitBoundary
      P G R hunit)

/-- Unit-boundary triples also satisfy the accepted-edge goal vacuously, since
the graph-exceptional side is already true. -/
theorem dPlusGraphAcceptedEdgeGoal_of_unitBoundary
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hunit : T.UnitBoundary) :
    T.DPlusGraphAcceptedEdgeGoal P G R := by
  intro _hsmall hnotExceptional _hNoAccepted
  exact hnotExceptional (T.dPlusGraphExceptional_of_unitBoundary P hunit)

end ABCData

end ABD3
