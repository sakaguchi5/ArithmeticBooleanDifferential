/-
  ABD.ApparitionDepth3.HenselExistence

  Concrete one-step existence for X^d - 1 from a simple seed root.
-/

import ABD.ApparitionDepth3.HenselExpansion

namespace ApparitionDepth3

/-- A simple root modulo a prime has a compatible lift from every positive
level r to level r+1. -/
theorem henselOneStepExists_of_simpleRoot
    {seed p d : Nat} [Fact p.Prime]
    (hsimple : SimpleRootModP seed p d) :
    HenselOneStepExists seed p d := by
  intro r hr_pos omega hlift
  rcases exists_errorQuotient_of_lift hsimple hlift with ⟨q, hquot⟩
  have hderiv : IsUnit (derivativeAt omega p d) :=
    derivativeUnit_of_seedCongr hsimple hlift.1
  rcases exists_correctionDigit_of_derivativeUnit
      (omega := omega) (q := q) hderiv with ⟨t, hcorr⟩
  let omegaNext : Nat := correctedRepresentative omega t p r
  have hseedNext : BranchSeedModP seed omegaNext p := by
    dsimp [omegaNext]
    exact correctedRepresentative_seedCongr hr_pos hlift.1
  have hrootNext : RootAtLevel omegaNext p d (r + 1) := by
    dsimp [omegaNext]
    exact rootAtNextLevel_of_quotient_correction hr_pos hquot hcorr
  have hreduce :
      (omegaNext : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) := by
    dsimp [omegaNext]
    exact correctedRepresentative_reduce omega t p r
  unfold HenselCorrectionStep
  exact ⟨omegaNext, ⟨hseedNext, hrootNext⟩, hreduce⟩

end ApparitionDepth3
