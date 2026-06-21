import ABD.ABD3.Views.DPlusGraph.ResidualStep3NoAccepted
import ABD.ABD3.Views.DPlusGraph.Frontier

namespace ABD3

namespace ABCData

/-- Step 4 normal form: the residual unaccepted C-port mass dominates the
negative deficit product. -/
def UnacceptedCPortMassDominatesDeficit
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.NegativeDeficitProduct P < T.UnacceptedCPortMassProduct P G R

/-- Step 4 of the residual C-port argument.

D+ dominance plus no accepted arithmetic edge forces the remaining unaccepted
C-port mass to dominate the deficit product. -/
theorem residual_step4_unacceptedDominatesDeficit_of_dplus_and_noAccepted
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hdom : T.CPortMassDominatesDeficit P)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.UnacceptedCPortMassDominatesDeficit P G R := by
  unfold UnacceptedCPortMassDominatesDeficit
  exact T.unacceptedCPortMassProduct_dominates_deficit_of_cPortMassDominatesDeficit_of_noAccepted
    P G R hdom hno

/-- Step 4, radical-small entry version. -/
theorem residual_step4_unacceptedDominatesDeficit_of_radicalSmall_and_noAccepted
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hsmall : T.RadicalSmall P)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.UnacceptedCPortMassDominatesDeficit P G R := by
  exact T.residual_step4_unacceptedDominatesDeficit_of_dplus_and_noAccepted
    P G R (T.residual_step1_cPortMassDominatesDeficit_of_radicalSmall P hsmall) hno

/-- The next frontier goal after Steps 1--4.

Read this as: once the residual unaccepted C-port mass dominates the deficit,
the triple should fall to the graph-exceptional side.  This is intentionally
weaker and more local than directly proving `exceptional` from D+ dominance. -/
def ResidualUnacceptedDominanceForcesGraphExceptionalGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.UnacceptedCPortMassDominatesDeficit P G R →
    T.DPlusGraphExceptional P

/-- A residual-dominance contradiction goal implies the existing low-absorption
contradiction goal. -/
theorem dPlusLowAbsorptionContradictionGoal_of_residualUnacceptedDominanceGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.ResidualUnacceptedDominanceForcesGraphExceptionalGoal P G R) :
    T.DPlusLowAbsorptionContradictionGoal P G R := by
  unfold DPlusLowAbsorptionContradictionGoal
  intro hdom hlow
  apply hgoal
  unfold UnacceptedCPortMassDominatesDeficit
  exact T.unacceptedCPortMassProduct_dominates_deficit_of_cPortMassDominatesDeficit_of_low
    P G R hdom hlow

/-- A residual-dominance contradiction goal is enough to recover the D+ graph
accepted-edge goal. -/
theorem dPlusGraphAcceptedEdgeGoal_of_residualUnacceptedDominanceGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.ResidualUnacceptedDominanceForcesGraphExceptionalGoal P G R) :
    T.DPlusGraphAcceptedEdgeGoal P G R := by
  exact T.dPlusGraphAcceptedEdgeGoal_of_lowAbsorptionContradictionGoal
    P G R
    (T.dPlusLowAbsorptionContradictionGoal_of_residualUnacceptedDominanceGoal
      P G R hgoal)

/-- Radical-small plus no accepted arithmetic edge falls to the graph-exceptional
side, assuming only the residual-dominance frontier goal. -/
theorem dPlusGraphExceptional_of_radicalSmall_of_noAccepted_of_residualUnacceptedDominanceGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.ResidualUnacceptedDominanceForcesGraphExceptionalGoal P G R)
    (hsmall : T.RadicalSmall P)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.DPlusGraphExceptional P := by
  exact hgoal
    (T.residual_step4_unacceptedDominatesDeficit_of_radicalSmall_and_noAccepted
      P G R hsmall hno)

end ABCData

end ABD3
