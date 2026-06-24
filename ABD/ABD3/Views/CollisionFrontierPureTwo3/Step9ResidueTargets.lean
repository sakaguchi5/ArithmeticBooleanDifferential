import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step8ExponentCoprime

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Conditional mod-16 source equation target.

Unlike mod `8`, this needs the extra hypothesis `4 ≤ w`. -/
def SourceSumModSixteenGoal (F : NormalForm T P) : Prop :=
  (F.p ^ F.u + F.q ^ F.v) % 16 = 0

/-- Source equation modulo `3`.  The right hand side is periodic, not zero. -/
def SourceSumModThreeGoal (F : NormalForm T P) : Prop :=
  F.SourceSumModGoal 3

/-- Source equation modulo `5`.  The right hand side is periodic, not zero. -/
def SourceSumModFiveGoal (F : NormalForm T P) : Prop :=
  F.SourceSumModGoal 5

/-- Mod-16 source equation, conditional on `4 ≤ w`. -/
theorem source_sum_mod_sixteen_of_four_le_w
    (F : NormalForm T P) (h4 : 4 ≤ F.w) :
    F.SourceSumModSixteenGoal := by
  change (F.p ^ F.u + F.q ^ F.v) % (2 ^ 4) = 0
  exact F.source_sum_mod_two_pow_zero_of_le_w h4

/-- Source equation modulo `3`. -/
theorem source_sum_mod_three (F : NormalForm T P) :
    F.SourceSumModThreeGoal := by
  exact F.source_sum_mod_goal 3

/-- Source equation modulo `5`. -/
theorem source_sum_mod_five (F : NormalForm T P) :
    F.SourceSumModFiveGoal := by
  exact F.source_sum_mod_goal 5

/-- Residue-extension targets for the canonical PureTwo3 layer.

This is intentionally light: mod-3 and mod-5 are recorded as source congruences,
while mod-16 is conditional on `4 ≤ w`.  Later steps can refine these into
period classifications. -/
structure ResidueTargets (F : NormalForm T P) where
  mod_three : F.SourceSumModThreeGoal
  mod_five : F.SourceSumModFiveGoal
  mod_sixteen_of_four_le_w : 4 ≤ F.w → F.SourceSumModSixteenGoal

def ResidueTargetsGoal (F : NormalForm T P) : Prop :=
  Nonempty (ResidueTargets F)

/-- Realization of the residue-extension shell. -/
theorem residueTargets_real (F : NormalForm T P) :
    ResidueTargets F :=
  { mod_three := F.source_sum_mod_three
    mod_five := F.source_sum_mod_five
    mod_sixteen_of_four_le_w := fun h4 =>
      F.source_sum_mod_sixteen_of_four_le_w h4 }

theorem residueTargetsGoal (F : NormalForm T P) :
    F.ResidueTargetsGoal :=
  ⟨F.residueTargets_real⟩

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
