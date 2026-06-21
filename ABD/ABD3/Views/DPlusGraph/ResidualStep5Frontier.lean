import ABD.ABD3.Views.DPlusGraph.ResidualFrontier

namespace ABD3

namespace ABCData

/-- Step 5 goal: residual unaccepted C-port dominance forces the residual
frontier.

This is the intended replacement for trying to prove
`UnacceptedCPortMassDominatesDeficit -> DPlusGraphExceptional` in one jump. -/
def ResidualUnacceptedDominanceForcesFrontierGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.UnacceptedCPortMassDominatesDeficit P G R →
    T.ResidualFrontier P G R

/-- Step 5 bridge: the frontier goal implies the stronger graph-exceptional goal
used by Step 4. -/
theorem residualUnacceptedDominanceForcesGraphExceptionalGoal_of_frontierGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hfrontier :
      T.ResidualUnacceptedDominanceForcesFrontierGoal P G R) :
    T.ResidualUnacceptedDominanceForcesGraphExceptionalGoal P G R := by
  intro hresidual
  exact T.dPlusGraphExceptional_of_residualFrontier P G R
    (hfrontier hresidual)

/-- Step 5 bridge to the existing low-absorption contradiction goal. -/
theorem dPlusLowAbsorptionContradictionGoal_of_residualFrontierGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hfrontier :
      T.ResidualUnacceptedDominanceForcesFrontierGoal P G R) :
    T.DPlusLowAbsorptionContradictionGoal P G R := by
  exact T.dPlusLowAbsorptionContradictionGoal_of_residualUnacceptedDominanceGoal
    P G R
    (T.residualUnacceptedDominanceForcesGraphExceptionalGoal_of_frontierGoal
      P G R hfrontier)

/-- Step 5 bridge to the accepted-edge goal. -/
theorem dPlusGraphAcceptedEdgeGoal_of_residualFrontierGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hfrontier :
      T.ResidualUnacceptedDominanceForcesFrontierGoal P G R) :
    T.DPlusGraphAcceptedEdgeGoal P G R := by
  exact T.dPlusGraphAcceptedEdgeGoal_of_residualUnacceptedDominanceGoal
    P G R
    (T.residualUnacceptedDominanceForcesGraphExceptionalGoal_of_frontierGoal
      P G R hfrontier)

/-- Radical-small plus no accepted arithmetic edge falls to the residual frontier,
assuming only the Step 5 frontier goal. -/
theorem residualFrontier_of_radicalSmall_of_noAccepted_of_frontierGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hfrontier :
      T.ResidualUnacceptedDominanceForcesFrontierGoal P G R)
    (hsmall : T.RadicalSmall P)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.ResidualFrontier P G R := by
  exact hfrontier
    (T.residual_step4_unacceptedDominatesDeficit_of_radicalSmall_and_noAccepted
      P G R hsmall hno)

/-- Radical-small plus no accepted arithmetic edge falls to graph-exceptional,
assuming the Step 5 frontier goal. -/
theorem dPlusGraphExceptional_of_radicalSmall_of_noAccepted_of_frontierGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hfrontier :
      T.ResidualUnacceptedDominanceForcesFrontierGoal P G R)
    (hsmall : T.RadicalSmall P)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.DPlusGraphExceptional P := by
  exact T.dPlusGraphExceptional_of_residualFrontier P G R
    (T.residualFrontier_of_radicalSmall_of_noAccepted_of_frontierGoal
      P G R hfrontier hsmall hno)

end ABCData

end ABD3
