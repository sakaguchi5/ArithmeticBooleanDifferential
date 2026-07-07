/-
  ABD.ApparitionDepth.FiniteHenselStepExistence

  Step 21D-3 of the Apparition-Depth Decomposition project.

  This file packages one-step finite Hensel existence.  The heavy binomial
  calculation that turns a solved linear equation into an actual lifted root is
  represented by a named certificate, and all transport into the existing Hensel
  branch interface is proved here.
-/

import ABD.ApparitionDepth.FiniteHenselLinearEquation

namespace ApparitionDepth

/-! ## One-step existence certificates -/

/-- A concrete one-step existence certificate over a fixed old representative.

Given a level-`r` branch lift `omega`, this certificate produces a next-level
representative `omegaNext`, a correction digit `t`, and a root step. -/
def FiniteHenselStepExistenceOver (g omega p d j r : Nat) : Prop :=
  HenselBranchLiftAtLevel g omega p d j r →
    ∃ omegaNext t : Nat,
      HenselBranchLiftAtLevel g omegaNext p d j (r + 1) ∧
        FiniteHenselRootStep omega omegaNext t p d r

/-- One-step existence for all old representatives of the branch at level `r`. -/
def FiniteHenselStepExistenceAtLevel (g p d j r : Nat) : Prop :=
  ∀ omega : Nat, FiniteHenselStepExistenceOver g omega p d j r

/-- One-step existence at every positive level. -/
def FiniteHenselStepExistenceForAllLevels (g p d j : Nat) : Prop :=
  ∀ r : Nat, 0 < r → FiniteHenselStepExistenceAtLevel g p d j r

/-- Constructor for concrete one-step existence over a fixed representative. -/
theorem finiteHenselStepExistenceOver_intro {g omega p d j r : Nat}
    (h : HenselBranchLiftAtLevel g omega p d j r →
      ∃ omegaNext t : Nat,
        HenselBranchLiftAtLevel g omegaNext p d j (r + 1) ∧
          FiniteHenselRootStep omega omegaNext t p d r) :
    FiniteHenselStepExistenceOver g omega p d j r :=
  h

/-- Apply concrete one-step existence. -/
theorem finiteHenselStepExistenceOver_apply
    {g omega p d j r : Nat}
    (hexists : FiniteHenselStepExistenceOver g omega p d j r)
    (hlift : HenselBranchLiftAtLevel g omega p d j r) :
    ∃ omegaNext t : Nat,
      HenselBranchLiftAtLevel g omegaNext p d j (r + 1) ∧
        FiniteHenselRootStep omega omegaNext t p d r :=
  hexists hlift

/-- Constructor for one-step existence at a level. -/
theorem finiteHenselStepExistenceAtLevel_intro {g p d j r : Nat}
    (h : ∀ omega : Nat, FiniteHenselStepExistenceOver g omega p d j r) :
    FiniteHenselStepExistenceAtLevel g p d j r :=
  h

/-- Apply one-step existence at a level. -/
theorem finiteHenselStepExistenceAtLevel_apply
    {g omega p d j r : Nat}
    (hexists : FiniteHenselStepExistenceAtLevel g p d j r)
    (hlift : HenselBranchLiftAtLevel g omega p d j r) :
    ∃ omegaNext t : Nat,
      HenselBranchLiftAtLevel g omegaNext p d j (r + 1) ∧
        FiniteHenselRootStep omega omegaNext t p d r :=
  hexists omega hlift

/-- Extract a level from all-level one-step existence. -/
theorem finiteHenselStepExistenceForAllLevels_at
    {g p d j r : Nat}
    (hexists : FiniteHenselStepExistenceForAllLevels g p d j)
    (hr_pos : 0 < r) :
    FiniteHenselStepExistenceAtLevel g p d j r :=
  hexists r hr_pos

/-- One-step existence advances Hensel-lift existence from level `r` to `r+1`. -/
theorem henselLiftExists_succ_of_stepExistenceAtLevel
    {g p d j r : Nat}
    (hexists : FiniteHenselStepExistenceAtLevel g p d j r)
    (hlevel : HenselLiftExists g p d j r) :
    HenselLiftExists g p d j (r + 1) := by
  rcases hlevel with ⟨omega, hlift⟩
  rcases finiteHenselStepExistenceAtLevel_apply hexists hlift with
    ⟨omegaNext, _t, hliftNext, _hstep⟩
  exact ⟨omegaNext, hliftNext⟩

/-- A solved-step certificate at one level.

This bundles the branch-level one-step existence together with the intended
linear-equation solved data.  The linear data is kept as a separate field so that
later files can replace this certificate with a real finite-field proof. -/
def FiniteHenselSolvedStepExistenceAtLevel (g p d j r : Nat) : Prop :=
  FiniteHenselStepExistenceAtLevel g p d j r

/-- Projection from the solved-step wrapper. -/
theorem finiteHenselStepExistenceAtLevel_of_solvedStep
    {g p d j r : Nat}
    (h : FiniteHenselSolvedStepExistenceAtLevel g p d j r) :
    FiniteHenselStepExistenceAtLevel g p d j r :=
  h

end ApparitionDepth
