import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step9ResidueTargets

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Canonical hard elementary package for PureTwo3.

Compared with PureTwo2, this package is organized in standard-proof order:

* prime/lower bounds,
* mod-8 constraints,
* exponent coprimality,
* residue-extension shell. -/
structure HardElementaryGoals (F : NormalForm T P) where
  bounds : BasicBounds F
  mod_eight : ModEightConstraints F
  exponent_coprime : F.ExponentCoprimeGoal
  residue : ResidueTargets F

def HardElementaryGoalsGoal (F : NormalForm T P) : Prop :=
  Nonempty (HardElementaryGoals F)

/-- Extract exponent coprimality from the canonical hard elementary package. -/
theorem exponentCoprime_of_hardElementaryGoals
    (F : NormalForm T P)
    (H : HardElementaryGoals F) :
    F.ExponentCoprimeGoal :=
  H.exponent_coprime

/-- Realization of the PureTwo3 hard elementary package. -/
theorem hardElementaryGoals (F : NormalForm T P) :
    HardElementaryGoals F :=
  { bounds := F.basicBounds_real
    mod_eight := F.modEightConstraints_real
    exponent_coprime := F.exponentCoprime
    residue := F.residueTargets_real }

theorem hardElementaryGoalsGoal (F : NormalForm T P) :
    F.HardElementaryGoalsGoal :=
  ⟨F.hardElementaryGoals⟩

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
