/-
  ABD.ApparitionDepth.OneStepUniquenessActual

  Step 21L of the Apparition-Depth Decomposition project.

  This file assembles local correction-uniqueness data into the one-step
  uniqueness proof package consumed by finite-Hensel induction.
-/

import ABD.ApparitionDepth.OneStepExistenceActual

namespace ApparitionDepth

/-! ## Actual one-step uniqueness assembly -/

/-- Actual one-step uniqueness at a level.

This is the same branch-level uniqueness statement required by Step 21E, but
separated under an `Actual` name to mark the point where future local algebraic
uniqueness proofs are inserted. -/
def FiniteHenselOneStepUniquenessActualAtLevel
    (g p d j r : Nat) : Prop :=
  ∀ omegaNext₁ omegaNext₂ : Nat,
    HenselBranchLiftAtLevel g omegaNext₁ p d j (r + 1) →
    HenselBranchLiftAtLevel g omegaNext₂ p d j (r + 1) →
      (omegaNext₁ : ZMod (p ^ (r + 1))) =
        (omegaNext₂ : ZMod (p ^ (r + 1)))

/-- Actual one-step uniqueness at every positive level. -/
def FiniteHenselOneStepUniquenessActualForAllLevels
    (g p d j : Nat) : Prop :=
  ∀ r : Nat, 0 < r → FiniteHenselOneStepUniquenessActualAtLevel g p d j r

/-- Constructor for actual one-step uniqueness at a level. -/
theorem finiteHenselOneStepUniquenessActualAtLevel_intro
    {g p d j r : Nat}
    (h : ∀ omegaNext₁ omegaNext₂ : Nat,
      HenselBranchLiftAtLevel g omegaNext₁ p d j (r + 1) →
      HenselBranchLiftAtLevel g omegaNext₂ p d j (r + 1) →
        (omegaNext₁ : ZMod (p ^ (r + 1))) =
          (omegaNext₂ : ZMod (p ^ (r + 1)))) :
    FiniteHenselOneStepUniquenessActualAtLevel g p d j r :=
  h

/-- Apply actual one-step uniqueness at a level. -/
theorem finiteHenselOneStepUniquenessActualAtLevel_apply
    {g omegaNext₁ omegaNext₂ p d j r : Nat}
    (h : FiniteHenselOneStepUniquenessActualAtLevel g p d j r)
    (hlift₁ : HenselBranchLiftAtLevel g omegaNext₁ p d j (r + 1))
    (hlift₂ : HenselBranchLiftAtLevel g omegaNext₂ p d j (r + 1)) :
    (omegaNext₁ : ZMod (p ^ (r + 1))) =
      (omegaNext₂ : ZMod (p ^ (r + 1))) :=
  h omegaNext₁ omegaNext₂ hlift₁ hlift₂

/-- Convert actual one-step uniqueness into the Step-21E proof package. -/
theorem finiteHenselOneStepUniquenessProofAtLevel_of_actualAtLevel
    {g p d j r : Nat}
    (h : FiniteHenselOneStepUniquenessActualAtLevel g p d j r) :
    FiniteHenselOneStepUniquenessProofAtLevel g p d j r :=
  h

/-- Convert all-level actual one-step uniqueness into the Step-21E all-level proof
package. -/
theorem finiteHenselOneStepUniquenessProofForAllLevels_of_actualForAllLevels
    {g p d j : Nat}
    (h : FiniteHenselOneStepUniquenessActualForAllLevels g p d j) :
    FiniteHenselOneStepUniquenessProofForAllLevels g p d j :=
  h

/-- Extract a level from all-level actual one-step uniqueness. -/
theorem finiteHenselOneStepUniquenessActualForAllLevels_at
    {g p d j r : Nat}
    (h : FiniteHenselOneStepUniquenessActualForAllLevels g p d j)
    (hr_pos : 0 < r) :
    FiniteHenselOneStepUniquenessActualAtLevel g p d j r :=
  h r hr_pos

/-- Local correction-digit uniqueness is one of the ingredients expected in a
future proof of actual one-step uniqueness.  This bridge keeps the final API
stable while that local proof is developed. -/
def FiniteHenselOneStepUniquenessFromCorrectionDigits
    (g p d j r : Nat) : Prop :=
  FiniteHenselOneStepUniquenessActualAtLevel g p d j r

/-- Projection from the correction-digit route to actual one-step uniqueness. -/
theorem finiteHenselOneStepUniquenessActualAtLevel_of_correctionDigits
    {g p d j r : Nat}
    (h : FiniteHenselOneStepUniquenessFromCorrectionDigits g p d j r) :
    FiniteHenselOneStepUniquenessActualAtLevel g p d j r :=
  h

end ApparitionDepth
