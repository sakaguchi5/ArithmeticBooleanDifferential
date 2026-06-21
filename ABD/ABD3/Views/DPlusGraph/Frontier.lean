import ABD.ABD3.Views.DPlusGraph.Absorption

namespace ABD3

namespace ABCData

/-- First ABD3-only exceptional family for the graph argument: the full support is
so small that the C-port graph may have too little room to force a cheap edge.

The threshold is intentionally conservative and can be refined after computation. -/
def SupportSmallExceptional (T : ABCData) : Prop :=
  T.supportABC.card ≤ 3

/-- Second ABD3-only exceptional family: the positive C-surplus side consists of
at most one port.  This captures prime-power C frontiers such as examples where
all D+ mass is concentrated at a single C-port. -/
def SurplusIsolatedExceptional (T : ABCData) (P : PowerData) : Prop :=
  (T.CSurplusPorts P).card ≤ 1

/-- Combined ABD3 graph exceptional side. -/
def DPlusGraphExceptional
    (T : ABCData) (P : PowerData) : Prop :=
  T.UnitBoundary ∨ T.SupportSmallExceptional ∨ T.SurplusIsolatedExceptional P

/-- The D++ absorption contradiction goal.

Read this as: if D+ says C-port mass dominates deficit mass, and nevertheless
all positive ports have low absorption into A/B, then the triple must lie in the
ABD3 graph exceptional side.  This is the ABD3-only replacement for the ABD2
route-level surplus-absorption assumption. -/
def DPlusLowAbsorptionContradictionGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CPortMassDominatesDeficit P →
    T.CPortAbsorptionLow P G R →
      T.DPlusGraphExceptional P

/-- A radical-small triple with no accepted arithmetic edge falls to the ABD3
D+ graph exceptional side, assuming the low-absorption contradiction goal. -/
theorem dPlusGraphExceptional_of_radicalSmall_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.DPlusLowAbsorptionContradictionGoal P G R)
    (hsmall : T.RadicalSmall P)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.DPlusGraphExceptional P := by
  have hdom : T.CPortMassDominatesDeficit P :=
    T.theoremDPlus_as_cPortMassDominance P hsmall
  have hlow : T.CPortAbsorptionLow P G R :=
    T.cPortAbsorptionLow_of_noAcceptedArithmeticEdge P G R hno
  exact hgoal hdom hlow

/-- ABD3 D+ graph coverage goal: outside the graph exceptional side, a
radical-small triple must have an accepted arithmetic edge. -/
def DPlusGraphAcceptedEdgeGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.RadicalSmall P →
    ¬ T.DPlusGraphExceptional P →
      ¬ T.NoAcceptedArithmeticEdge P G R

/-- The low-absorption contradiction goal gives the accepted-edge goal. -/
theorem dPlusGraphAcceptedEdgeGoal_of_lowAbsorptionContradictionGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.DPlusLowAbsorptionContradictionGoal P G R) :
    T.DPlusGraphAcceptedEdgeGoal P G R := by
  intro hsmall hnotExceptional hno
  have hexceptional : T.DPlusGraphExceptional P :=
    T.dPlusGraphExceptional_of_radicalSmall_of_noAcceptedArithmeticEdge
      P G R hgoal hsmall hno
  exact hnotExceptional hexceptional

/-- A more explicit non-exceptional-entry version. -/
theorem not_noAcceptedArithmeticEdge_of_radicalSmall_of_not_graphExceptional
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.DPlusLowAbsorptionContradictionGoal P G R)
    (hsmall : T.RadicalSmall P)
    (hnotExceptional : ¬ T.DPlusGraphExceptional P) :
    ¬ T.NoAcceptedArithmeticEdge P G R := by
  exact T.dPlusGraphAcceptedEdgeGoal_of_lowAbsorptionContradictionGoal
    P G R hgoal hsmall hnotExceptional

end ABCData

end ABD3
