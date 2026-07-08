/-
  ABD.ApparitionDepth.OneStepExistenceActual

  Step 21K of the Apparition-Depth Decomposition project.

  This file assembles quotient, correction, truncation, and next-lift data into the
  one-step existence proof package consumed by the finite-Hensel induction.
-/

import ABD.ApparitionDepth.HigherTermsVanishProof

namespace ApparitionDepth

/-! ## Actual one-step existence assembly -/

/-- Local data sufficient to produce one one-step existence proof over a fixed old
lift.

The heavy algebraic ingredients are now localized as:
* a normalized quotient `q`,
* a candidate next representative `omegaNext`,
* a correction digit `t`,
* a branch lift at level `r+1`,
* a root-step relation,
* and the certificate that the correction kills the error.
-/
def FiniteHenselOneStepExistenceActualOver
    (g omega p d j r : Nat) : Prop :=
  HenselBranchLiftAtLevel g omega p d j r →
    ∃ q omegaNext t : Nat,
      HenselBranchLiftAtLevel g omegaNext p d j (r + 1) ∧
        FiniteHenselRootStep omega omegaNext t p d r ∧
          FiniteHenselCorrectionKillsError omega omegaNext q t p d r

/-- Level-wise version of the actual one-step existence assembly. -/
def FiniteHenselOneStepExistenceActualAtLevel
    (g p d j r : Nat) : Prop :=
  ∀ omega : Nat, FiniteHenselOneStepExistenceActualOver g omega p d j r

/-- All-level version of the actual one-step existence assembly. -/
def FiniteHenselOneStepExistenceActualForAllLevels
    (g p d j : Nat) : Prop :=
  ∀ r : Nat, 0 < r → FiniteHenselOneStepExistenceActualAtLevel g p d j r

/-- Constructor for actual one-step existence over a fixed old lift. -/
theorem finiteHenselOneStepExistenceActualOver_intro
    {g omega p d j r : Nat}
    (h : HenselBranchLiftAtLevel g omega p d j r →
      ∃ q omegaNext t : Nat,
        HenselBranchLiftAtLevel g omegaNext p d j (r + 1) ∧
          FiniteHenselRootStep omega omegaNext t p d r ∧
            FiniteHenselCorrectionKillsError omega omegaNext q t p d r) :
    FiniteHenselOneStepExistenceActualOver g omega p d j r :=
  h

/-- Convert actual one-step existence over a fixed old lift into the Step-21E proof
package. -/
theorem finiteHenselOneStepExistenceProofOver_of_actualOver
    {g omega p d j r : Nat}
    (h : FiniteHenselOneStepExistenceActualOver g omega p d j r) :
    FiniteHenselOneStepExistenceProofOver g omega p d j r :=
  h

/-- Convert level-wise actual one-step existence into the Step-21E proof package. -/
theorem finiteHenselOneStepExistenceProofAtLevel_of_actualAtLevel
    {g p d j r : Nat}
    (h : FiniteHenselOneStepExistenceActualAtLevel g p d j r) :
    FiniteHenselOneStepExistenceProofAtLevel g p d j r :=
  h

/-- Convert all-level actual one-step existence into the Step-21E all-level package. -/
theorem finiteHenselOneStepExistenceProofForAllLevels_of_actualForAllLevels
    {g p d j : Nat}
    (h : FiniteHenselOneStepExistenceActualForAllLevels g p d j) :
    FiniteHenselOneStepExistenceProofForAllLevels g p d j :=
  h

/-- A focused constructor: if for every old lift we can provide quotient,
correction, next lift, root step, and error-killing data, then we have actual
one-step existence at the level. -/
theorem finiteHenselOneStepExistenceActualAtLevel_intro
    {g p d j r : Nat}
    (h : ∀ omega : Nat,
      HenselBranchLiftAtLevel g omega p d j r →
        ∃ q omegaNext t : Nat,
          HenselBranchLiftAtLevel g omegaNext p d j (r + 1) ∧
            FiniteHenselRootStep omega omegaNext t p d r ∧
              FiniteHenselCorrectionKillsError omega omegaNext q t p d r) :
    FiniteHenselOneStepExistenceActualAtLevel g p d j r :=
  h

/-- Extract a level from the all-level actual one-step existence package. -/
theorem finiteHenselOneStepExistenceActualForAllLevels_at
    {g p d j r : Nat}
    (h : FiniteHenselOneStepExistenceActualForAllLevels g p d j)
    (hr_pos : 0 < r) :
    FiniteHenselOneStepExistenceActualAtLevel g p d j r :=
  h r hr_pos

end ApparitionDepth
