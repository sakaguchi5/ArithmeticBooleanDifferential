/-
  ABD.ApparitionDepth.StepUniquenessProof

  Step 21E-6 of the Apparition-Depth Decomposition project.

  This file turns a local one-step uniqueness proof into the one-step uniqueness
  interface used by the finite-Hensel induction.
-/

import ABD.ApparitionDepth.StepExistenceProof

namespace ApparitionDepth

/-! ## One-step uniqueness proof package -/

/-- A concrete uniqueness proof for next-level branch lifts.

This is the branch-level uniqueness statement at `r+1`, phrased as the local
one-step proof object that later algebra should produce from the linear
correction uniqueness. -/
def FiniteHenselOneStepUniquenessProofAtLevel (g p d j r : Nat) : Prop :=
  ∀ omegaNext1 omegaNext2 : Nat,
    HenselBranchLiftAtLevel g omegaNext1 p d j (r + 1) →
    HenselBranchLiftAtLevel g omegaNext2 p d j (r + 1) →
      (omegaNext1 : ZMod (p ^ (r + 1))) =
        (omegaNext2 : ZMod (p ^ (r + 1)))

/-- One-step uniqueness proof at every positive level. -/
def FiniteHenselOneStepUniquenessProofForAllLevels (g p d j : Nat) : Prop :=
  ∀ r : Nat, 0 < r → FiniteHenselOneStepUniquenessProofAtLevel g p d j r

/-- Constructor for one-step uniqueness proof at a level. -/
theorem finiteHenselOneStepUniquenessProofAtLevel_intro {g p d j r : Nat}
    (h : ∀ omegaNext1 omegaNext2 : Nat,
      HenselBranchLiftAtLevel g omegaNext1 p d j (r + 1) →
      HenselBranchLiftAtLevel g omegaNext2 p d j (r + 1) →
        (omegaNext1 : ZMod (p ^ (r + 1))) =
          (omegaNext2 : ZMod (p ^ (r + 1)))) :
    FiniteHenselOneStepUniquenessProofAtLevel g p d j r :=
  h

/-- Apply one-step uniqueness proof at a level. -/
theorem finiteHenselOneStepUniquenessProofAtLevel_apply
    {g omegaNext1 omegaNext2 p d j r : Nat}
    (hproof : FiniteHenselOneStepUniquenessProofAtLevel g p d j r)
    (hlift1 : HenselBranchLiftAtLevel g omegaNext1 p d j (r + 1))
    (hlift2 : HenselBranchLiftAtLevel g omegaNext2 p d j (r + 1)) :
    (omegaNext1 : ZMod (p ^ (r + 1))) =
      (omegaNext2 : ZMod (p ^ (r + 1))) :=
  hproof omegaNext1 omegaNext2 hlift1 hlift2

/-- Extract one level from all-level one-step uniqueness proof. -/
theorem finiteHenselOneStepUniquenessProofForAllLevels_at
    {g p d j r : Nat}
    (hproof : FiniteHenselOneStepUniquenessProofForAllLevels g p d j)
    (hr_pos : 0 < r) :
    FiniteHenselOneStepUniquenessProofAtLevel g p d j r :=
  hproof r hr_pos

/-- A one-step uniqueness proof gives the existing one-step uniqueness interface. -/
theorem finiteHenselStepUniqueAtLevel_of_oneStepUniquenessProofAtLevel
    {g p d j r : Nat}
    (hproof : FiniteHenselOneStepUniquenessProofAtLevel g p d j r) :
    FiniteHenselStepUniqueAtLevel g p d j r := by
  intro omegaNext1 omegaNext2 hlift1 hlift2
  exact finiteHenselOneStepUniquenessProofAtLevel_apply hproof hlift1 hlift2

/-- All-level one-step uniqueness proof gives the existing all-level one-step
uniqueness interface. -/
theorem finiteHenselStepUniqueForAllLevels_of_oneStepUniquenessProofForAllLevels
    {g p d j : Nat}
    (hproof : FiniteHenselOneStepUniquenessProofForAllLevels g p d j) :
    FiniteHenselStepUniqueForAllLevels g p d j :=
  fun _r hr_pos =>
    finiteHenselStepUniqueAtLevel_of_oneStepUniquenessProofAtLevel
      (finiteHenselOneStepUniquenessProofForAllLevels_at hproof hr_pos)

/-- Linear-correction uniqueness proof for two concrete correction digits.  This is
kept as a separate local certificate because the final algebraic proof will show
that equality of next lifts forces equality of the corresponding correction
classes modulo `p`. -/
def FiniteHenselCorrectionDigitsUnique
    (omega q p d : Nat) : Prop :=
  FiniteHenselCorrectionSolutionUnique omega q p d

/-- Projection from correction-digit uniqueness to the correction-solution
uniqueness interface. -/
theorem finiteHenselCorrectionSolutionUnique_of_digitsUnique
    {omega q p d : Nat}
    (h : FiniteHenselCorrectionDigitsUnique omega q p d) :
    FiniteHenselCorrectionSolutionUnique omega q p d :=
  h

end ApparitionDepth
