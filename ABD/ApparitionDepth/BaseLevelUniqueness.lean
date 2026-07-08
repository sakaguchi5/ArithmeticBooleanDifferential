/-
  ABD.ApparitionDepth.BaseLevelUniqueness

  Step 21F of the Apparition-Depth Decomposition project.

  This file proves the base-level uniqueness required by the finite-Hensel
  induction.  At level `p^1`, two Hensel branch lifts of the same branch seed are
  congruent modulo `p`, because both reduce to the same branch seed modulo `p`.
-/

import ABD.ApparitionDepth.FiniteHenselOneStepFinal

namespace ApparitionDepth

/-! ## Base-level uniqueness -/

/-- Level-one Hensel uniqueness follows directly from the branch-seed equality.

At precision `p^1`, every `HenselBranchLiftAtLevel` carries the condition that
its representative is equal to the same `branchSeedValue` in `ZMod p`. -/
theorem henselLiftUniqueAtLevel_one_of_branchSeed {g p d j : Nat} :
    HenselLiftUniqueAtLevel g p d j 1 := by
  intro omega₁ omega₂ hlift₁ hlift₂
  have hseed₁ : BranchSeedModP g omega₁ p d j :=
    henselBranchLiftAtLevel_seed hlift₁
  have hseed₂ : BranchSeedModP g omega₂ p d j :=
    henselBranchLiftAtLevel_seed hlift₂
  have h₁ : (omega₁ : ZMod p) = branchSeedValue g p d j :=
    branchSeedModP_seedValue hseed₁
  have h₂ : (omega₂ : ZMod p) = branchSeedValue g p d j :=
    branchSeedModP_seedValue hseed₂
  have h : (omega₁ : ZMod p) = (omega₂ : ZMod p) := by
    calc
      (omega₁ : ZMod p) = branchSeedValue g p d j := h₁
      _ = (omega₂ : ZMod p) := h₂.symm
  rw [show p ^ 1 = p by simp]
  exact h

/-- The base uniqueness certificate required by the finite-Hensel induction. -/
theorem finiteHenselBaseUniqueAtLevelOne_of_branchSeed {g p d j : Nat} :
    FiniteHenselBaseUniqueAtLevelOne g p d j :=
  henselLiftUniqueAtLevel_one_of_branchSeed

/-- A convenience constructor for `FiniteHenselInductionInput` when the only
remaining data are the all-level one-step existence and one-step uniqueness
certificates. -/
theorem finiteHenselInductionInput_of_steps {g p d j : Nat}
    (hexists : FiniteHenselStepExistenceForAllLevels g p d j)
    (huniq : FiniteHenselStepUniqueForAllLevels g p d j) :
    FiniteHenselInductionInput g p d j :=
  finiteHenselInductionInput_intro
    finiteHenselBaseUniqueAtLevelOne_of_branchSeed
    hexists
    huniq

/-- One-step proof input follows once the all-level one-step proof packages are
available; base-level uniqueness is automatic from the branch seed. -/
theorem finiteHenselOneStepProofInput_of_oneStepProofs {g p d j : Nat}
    (hexists : FiniteHenselOneStepExistenceProofForAllLevels g p d j)
    (huniq : FiniteHenselOneStepUniquenessProofForAllLevels g p d j) :
    FiniteHenselOneStepProofInput g p d j :=
  finiteHenselOneStepProofInput_intro
    finiteHenselBaseUniqueAtLevelOne_of_branchSeed
    hexists
    huniq

end ApparitionDepth
