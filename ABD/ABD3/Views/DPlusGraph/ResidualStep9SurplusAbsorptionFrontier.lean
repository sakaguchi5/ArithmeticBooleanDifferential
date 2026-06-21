import ABD.ABD3.Views.DPlusGraph.ResidualStep8RejectedNormalForm

namespace ABD3

namespace ABCData

/-- Step 9 frontier: the remaining hard case after Steps 4, 7, and 8.

It combines the global product statement from Step 4 with the local rejected-edge
normal form from Step 8, while excluding the easy support-small and unit-boundary
frontiers.  This is the precise place where the next real number-theoretic lemma
must act. -/
def SurplusAbsorptionFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.UnacceptedCPortMassDominatesDeficit P G R ∧
    T.RejectedEdgeNormalForm P G R ∧
      T.ResidualSupportNotSmallConcrete P G R ∧
        ¬ T.ResidualUnitBoundary

/-- Step 9 goal: the surplus-absorption frontier should force radical-large.

This is the next boss after Step 8.  It says that if all edges are rejected and
the unaccepted C-port mass still dominates the deficit, then, away from the
small-support and unit-boundary frontiers, the radical side must actually be
large. -/
def SurplusAbsorptionGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.SurplusAbsorptionFrontier P G R → T.RadicalLarge P

/-- Radical-small plus no accepted edge enters the Step 9 surplus-absorption
frontier once support-small and unit-boundary have been excluded. -/
theorem step9Frontier_of_radSmall_noAccepted (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hsmall : T.RadicalSmall P)
    (hno : T.NoAcceptedArithmeticEdge P G R)
    (hnotSupport : T.ResidualSupportNotSmallConcrete P G R)
    (hnotUnit : ¬ T.ResidualUnitBoundary) :
    T.SurplusAbsorptionFrontier P G R := by
  unfold SurplusAbsorptionFrontier
  exact ⟨
    T.residual_step4_unacceptedDominatesDeficit_of_radicalSmall_and_noAccepted
      P G R hsmall hno,
    T.rejectedEdgeNormalForm_of_noAcceptedArithmeticEdge P G R hno,
    hnotSupport,
    hnotUnit
  ⟩

/-- A non-graph-exceptional triple has neither support-small nor unit-boundary,
so radical-small plus no accepted edge enters the Step 9 frontier. -/
theorem surplusAbsorptionFrontier_of_radicalSmall_of_noAccepted_of_notGraphExceptional
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hsmall : T.RadicalSmall P)
    (hno : T.NoAcceptedArithmeticEdge P G R)
    (hnotExceptional : ¬ T.DPlusGraphExceptional P) :
    T.SurplusAbsorptionFrontier P G R := by
  exact T.step9Frontier_of_radSmall_noAccepted
    P G R hsmall hno
    (T.residualSupportNotSmallConcrete_of_not_dPlusGraphExceptional P G R hnotExceptional)
    (by
      intro hunit
      exact hnotExceptional (T.dPlusGraphExceptional_of_unitBoundary P hunit))

/-- The Step 9 goal turns the hard no-accepted-edge frontier into radical-large. -/
theorem radicalLarge_of_radicalSmall_of_noAccepted_of_notGraphExceptional_of_surplusAbsorptionGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.SurplusAbsorptionGoal P G R)
    (hsmall : T.RadicalSmall P)
    (hno : T.NoAcceptedArithmeticEdge P G R)
    (hnotExceptional : ¬ T.DPlusGraphExceptional P) :
    T.RadicalLarge P := by
  exact hgoal
    (T.surplusAbsorptionFrontier_of_radicalSmall_of_noAccepted_of_notGraphExceptional
      P G R hsmall hno hnotExceptional)

/-- A final contrapositive interface: if radical-large is ruled out, then under
the Step 9 goal a radical-small non-exceptional triple cannot have no accepted
arithmetic edge. -/
theorem acceptedEdge_of_radSmall_nonexceptional (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.SurplusAbsorptionGoal P G R)
    (hsmall : T.RadicalSmall P)
    (hnotExceptional : ¬ T.DPlusGraphExceptional P)
    (hnotLarge : ¬ T.RadicalLarge P) :
    ¬ T.NoAcceptedArithmeticEdge P G R := by
  intro hno
  exact hnotLarge
    (T.radicalLarge_of_radicalSmall_of_noAccepted_of_notGraphExceptional_of_surplusAbsorptionGoal
      P G R hgoal hsmall hno hnotExceptional)

/-- Step 9 packaged as an accepted-edge goal with an explicit radical-large
exclusion.  This is the next target before replacing `¬ RadicalLarge` by a
concrete dangerous-zone normal form. -/
def SurplusAbsorptionAcceptedEdgeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.RadicalSmall P →
    ¬ T.DPlusGraphExceptional P →
      ¬ T.RadicalLarge P →
        ¬ T.NoAcceptedArithmeticEdge P G R

/-- The Step 9 surplus-absorption goal gives the packaged accepted-edge goal. -/
theorem surplusAbsorptionAcceptedEdgeGoal_of_surplusAbsorptionGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.SurplusAbsorptionGoal P G R) :
    T.SurplusAbsorptionAcceptedEdgeGoal P G R := by
  intro hsmall hnotExceptional hnotLarge
  exact T.acceptedEdge_of_radSmall_nonexceptional
    P G R hgoal hsmall hnotExceptional hnotLarge

end ABCData

end ABD3
