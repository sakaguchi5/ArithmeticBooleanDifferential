import ABD.ABD3.Views.CollisionFrontierPureTwo.Step4SyncGraph

namespace ABD3
namespace ABCData

/-- Pure two-power desynchronized frontier: the minimal single C-port model,
radical-small, but with no accepted arithmetic edge for the pure generators. -/
def PureTwoPowerDesyncFrontier
    (T : ABCData) (P : PowerData) (R : ℕ) : Prop :=
  ∃ F : PureTwoPowerNormalForm T P,
    T.RadicalSmall P ∧
      T.NoAcceptedArithmeticEdge P F.pureSyncGenerators R

/-- Pure two-power three-rejection frontier: the same frontier after expanding
`NoAcceptedArithmeticEdge` into the three concrete edges. -/
def PureTwoPowerThreeRejectionFrontier
    (T : ABCData) (P : PowerData) (R : ℕ) : Prop :=
  ∃ F : PureTwoPowerNormalForm T P,
    T.RadicalSmall P ∧ F.ThreeRejections R

/-- A singleton positive C-surplus port is isolated, hence belongs to the existing
ABD3 graph-exceptional side. -/
theorem surplusIsolatedExceptional_of_single_two
    (T : ABCData) (P : PowerData)
    (hports : T.CSurplusPorts P = {2}) :
    T.SurplusIsolatedExceptional P := by
  unfold SurplusIsolatedExceptional
  rw [hports]
  simp

/-- The pure two-power single-port side is already part of the current
`DPlusGraphExceptional` alternative.  This is intentional: this file is for
analyzing the exceptional frontier, not for proving the general accepted-edge
coverage theorem. -/
theorem dPlusGraphExceptional_of_single_two
    (T : ABCData) (P : PowerData)
    (hports : T.CSurplusPorts P = {2}) :
    T.DPlusGraphExceptional P := by
  exact Or.inr (Or.inr (T.surplusIsolatedExceptional_of_single_two P hports))

/-- Convert the desynchronized pure two-power frontier into the explicit
three-rejection frontier, once the single C-port and C-scale identifications are
available. -/
theorem threeRejectionFrontier_of_desyncFrontier
    (T : ABCData) (P : PowerData) (R : ℕ)
    (hports : T.CSurplusPorts P = {2})
    (hCscale : ∀ F : PureTwoPowerNormalForm T P,
      T.CPortCoeffNat 2 = F.pureGC) :
    T.PureTwoPowerDesyncFrontier P R →
      T.PureTwoPowerThreeRejectionFrontier P R := by
  intro hfrontier
  rcases hfrontier with ⟨F, hsmall, hno⟩
  exact ⟨F, hsmall,
    F.threeRejections_of_noAcceptedArithmeticEdge R hports (hCscale F) hno⟩

/-- A named future goal: after the pure two-power frontier is reduced to three
gcd/lcm rejections, prove a suitable finiteness or thinness statement.

This is deliberately a proposition, not a theorem: the all-variable case is the
hard Fermat-Catalan/ABC-facing part.  Fixed-support instances can later be
connected to `FixedSupportCollisionFinitenessGoal`. -/
def PureTwoPowerThinnessGoal
    (P : PowerData) (R : ℕ) : Prop :=
  ∃ reps : List ABCData,
    ∀ T : ABCData,
      T.PureTwoPowerThreeRejectionFrontier P R → T ∈ reps

/-- A reusable wrapper for any future proof of the pure two-power thinness goal. -/
theorem pureTwoPower_thin_of_goal
    (P : PowerData) (R : ℕ)
    (hgoal : PureTwoPowerThinnessGoal P R) :
    ∃ reps : List ABCData,
      ∀ T : ABCData,
        T.PureTwoPowerThreeRejectionFrontier P R → T ∈ reps := by
  exact hgoal

end ABCData
end ABD3
