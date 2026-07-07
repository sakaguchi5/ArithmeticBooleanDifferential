/-
  ABD.ApparitionDepth.FiniteHenselInduction

  Step 21D-5 of the Apparition-Depth Decomposition project.

  This file performs the finite-level induction once the one-step existence and
  uniqueness certificates are available.  Unlike the earlier theorem-shape files,
  this file contains an actual Nat induction over the precision level.
-/

import ABD.ApparitionDepth.FiniteHenselStepUniqueness

namespace ApparitionDepth

/-! ## Induction input -/

/-- Base-level uniqueness at level `p^1`.

Existence at level one is supplied by `HenselAdmissibleLiftAtLevelOne`; uniqueness
is kept as a separate finite-Hensel base certificate. -/
def FiniteHenselBaseUniqueAtLevelOne (g p d j : Nat) : Prop :=
  HenselLiftUniqueAtLevel g p d j 1

/-- The finite-Hensel induction input: uniqueness at level one, plus one-step
existence and uniqueness at every positive level. -/
def FiniteHenselInductionInput (g p d j : Nat) : Prop :=
  FiniteHenselBaseUniqueAtLevelOne g p d j ∧
    FiniteHenselStepExistenceForAllLevels g p d j ∧
      FiniteHenselStepUniqueForAllLevels g p d j

/-- Constructor for the finite-Hensel induction input. -/
theorem finiteHenselInductionInput_intro {g p d j : Nat}
    (hbase : FiniteHenselBaseUniqueAtLevelOne g p d j)
    (hexists : FiniteHenselStepExistenceForAllLevels g p d j)
    (huniq : FiniteHenselStepUniqueForAllLevels g p d j) :
    FiniteHenselInductionInput g p d j :=
  ⟨hbase, hexists, huniq⟩

/-- Projection: base uniqueness at level one. -/
theorem finiteHenselInductionInput_baseUnique {g p d j : Nat}
    (h : FiniteHenselInductionInput g p d j) :
    FiniteHenselBaseUniqueAtLevelOne g p d j :=
  h.1

/-- Projection: one-step existence for all positive levels. -/
theorem finiteHenselInductionInput_stepExists {g p d j : Nat}
    (h : FiniteHenselInductionInput g p d j) :
    FiniteHenselStepExistenceForAllLevels g p d j :=
  h.2.1

/-- Projection: one-step uniqueness for all positive levels. -/
theorem finiteHenselInductionInput_stepUnique {g p d j : Nat}
    (h : FiniteHenselInductionInput g p d j) :
    FiniteHenselStepUniqueForAllLevels g p d j :=
  h.2.2

/-- Level-one exists-unique from an admissible level-one lift and base uniqueness. -/
theorem henselLiftExistsUnique_one_of_admissible_baseUnique
    {g omega0 p d j : Nat}
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j)
    (hbase : FiniteHenselBaseUniqueAtLevelOne g p d j) :
    HenselLiftExistsUnique g p d j 1 :=
  henselLiftExistsUnique_intro
    (henselLiftExists_intro (henselAdmissibleLiftAtLevelOne_lift hadm))
    hbase

/-- Finite-Hensel induction: from level-one admissibility and the induction input,
get Hensel existence and uniqueness at any positive finite level. -/
theorem henselLiftExistsUnique_of_finiteHenselInductionInput
    {g omega0 p d j r : Nat}
    (hinput : FiniteHenselInductionInput g p d j)
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j)
    (hr_pos : 0 < r) :
    HenselLiftExistsUnique g p d j r := by
  revert hr_pos
  induction r with
  | zero =>
      intro hr_pos
      exact False.elim ((Nat.not_lt_zero 0) hr_pos)
  | succ n ih =>
      intro _hr_pos
      cases n with
      | zero =>
          exact henselLiftExistsUnique_one_of_admissible_baseUnique hadm
            (finiteHenselInductionInput_baseUnique hinput)
      | succ k =>
          have hk_pos : 0 < k + 1 := Nat.succ_pos k
          have hprev : HenselLiftExistsUnique g p d j (k + 1) := ih hk_pos
          have hexistsStep : FiniteHenselStepExistenceAtLevel g p d j (k + 1) :=
            finiteHenselStepExistenceForAllLevels_at
              (finiteHenselInductionInput_stepExists hinput) hk_pos
          have huniqStep : FiniteHenselStepUniqueAtLevel g p d j (k + 1) :=
            finiteHenselStepUniqueForAllLevels_at
              (finiteHenselInductionInput_stepUnique hinput) hk_pos
          exact henselLiftExistsUnique_succ_of_stepExistence_stepUniqueness
            hexistsStep huniqStep (henselLiftExistsUnique_exists hprev)

/-- Fixed-level finite-Hensel certificate produced by the induction input. -/
def FiniteHenselInductionCertificateAtLevel (g p d j r : Nat) : Prop :=
  ∀ omega0 : Nat,
    HenselAdmissibleLiftAtLevelOne g omega0 p d j →
      HenselLiftExistsUnique g p d j r

/-- All-level finite-Hensel certificate produced by the induction input. -/
def FiniteHenselInductionCertificateForAllLevels (g p d j : Nat) : Prop :=
  ∀ r : Nat, 0 < r → FiniteHenselInductionCertificateAtLevel g p d j r

/-- Build a fixed-level certificate from the induction input. -/
theorem finiteHenselInductionCertificateAtLevel_of_input
    {g p d j r : Nat}
    (hinput : FiniteHenselInductionInput g p d j)
    (hr_pos : 0 < r) :
    FiniteHenselInductionCertificateAtLevel g p d j r := by
  intro omega0 hadm
  exact henselLiftExistsUnique_of_finiteHenselInductionInput hinput hadm hr_pos

/-- Build an all-level certificate from the induction input. -/
theorem finiteHenselInductionCertificateForAllLevels_of_input
    {g p d j : Nat}
    (hinput : FiniteHenselInductionInput g p d j) :
    FiniteHenselInductionCertificateForAllLevels g p d j :=
  fun _r hr_pos => finiteHenselInductionCertificateAtLevel_of_input hinput hr_pos

end ApparitionDepth
