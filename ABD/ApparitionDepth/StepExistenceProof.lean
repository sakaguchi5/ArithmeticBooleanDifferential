/-
  ABD.ApparitionDepth.StepExistenceProof

  Step 21E-5 of the Apparition-Depth Decomposition project.

  This file turns the local quotient/truncation/linear-correction certificates
  into the one-step existence interface used by the finite-Hensel induction.
-/

import ABD.ApparitionDepth.LinearCorrectionSolve

namespace ApparitionDepth

/-! ## Local one-step existence proof package -/

/-- Concrete proof package for one-step existence over a fixed old lift.

Given an old branch lift, it produces:

* a normalized error quotient `q`;
* a next representative `omegaNext`;
* a correction digit `t`;
* a next-level branch lift;
* the root-step relation;
* the local quotient/binomial/linear certificate showing why the correction works.
-/
def FiniteHenselOneStepExistenceProofOver (g omega p d j r : Nat) : Prop :=
  HenselBranchLiftAtLevel g omega p d j r →
    ∃ q omegaNext t : Nat,
      HenselBranchLiftAtLevel g omegaNext p d j (r + 1) ∧
        FiniteHenselRootStep omega omegaNext t p d r ∧
          FiniteHenselCorrectionKillsError omega omegaNext q t p d r

/-- One-step existence proof at a whole level. -/
def FiniteHenselOneStepExistenceProofAtLevel (g p d j r : Nat) : Prop :=
  ∀ omega : Nat, FiniteHenselOneStepExistenceProofOver g omega p d j r

/-- One-step existence proof at every positive level. -/
def FiniteHenselOneStepExistenceProofForAllLevels (g p d j : Nat) : Prop :=
  ∀ r : Nat, 0 < r → FiniteHenselOneStepExistenceProofAtLevel g p d j r

/-- Constructor for one-step existence proof over a fixed old lift. -/
theorem finiteHenselOneStepExistenceProofOver_intro
    {g omega p d j r : Nat}
    (h : HenselBranchLiftAtLevel g omega p d j r →
      ∃ q omegaNext t : Nat,
        HenselBranchLiftAtLevel g omegaNext p d j (r + 1) ∧
          FiniteHenselRootStep omega omegaNext t p d r ∧
            FiniteHenselCorrectionKillsError omega omegaNext q t p d r) :
    FiniteHenselOneStepExistenceProofOver g omega p d j r :=
  h

/-- Apply one-step existence proof over a fixed old lift. -/
theorem finiteHenselOneStepExistenceProofOver_apply
    {g omega p d j r : Nat}
    (hproof : FiniteHenselOneStepExistenceProofOver g omega p d j r)
    (hlift : HenselBranchLiftAtLevel g omega p d j r) :
    ∃ q omegaNext t : Nat,
      HenselBranchLiftAtLevel g omegaNext p d j (r + 1) ∧
        FiniteHenselRootStep omega omegaNext t p d r ∧
          FiniteHenselCorrectionKillsError omega omegaNext q t p d r :=
  hproof hlift

/-- Constructor for level-wise one-step existence proof. -/
theorem finiteHenselOneStepExistenceProofAtLevel_intro {g p d j r : Nat}
    (h : ∀ omega : Nat, FiniteHenselOneStepExistenceProofOver g omega p d j r) :
    FiniteHenselOneStepExistenceProofAtLevel g p d j r :=
  h

/-- Apply level-wise one-step existence proof. -/
theorem finiteHenselOneStepExistenceProofAtLevel_apply
    {g omega p d j r : Nat}
    (hproof : FiniteHenselOneStepExistenceProofAtLevel g p d j r)
    (hlift : HenselBranchLiftAtLevel g omega p d j r) :
    ∃ q omegaNext t : Nat,
      HenselBranchLiftAtLevel g omegaNext p d j (r + 1) ∧
        FiniteHenselRootStep omega omegaNext t p d r ∧
          FiniteHenselCorrectionKillsError omega omegaNext q t p d r :=
  hproof omega hlift

/-- Extract one level from all-level one-step existence proof. -/
theorem finiteHenselOneStepExistenceProofForAllLevels_at
    {g p d j r : Nat}
    (hproof : FiniteHenselOneStepExistenceProofForAllLevels g p d j)
    (hr_pos : 0 < r) :
    FiniteHenselOneStepExistenceProofAtLevel g p d j r :=
  hproof r hr_pos

/-- A concrete one-step proof over a fixed old lift gives the existing one-step
existence-over interface. -/
theorem finiteHenselStepExistenceOver_of_oneStepProofOver
    {g omega p d j r : Nat}
    (hproof : FiniteHenselOneStepExistenceProofOver g omega p d j r) :
    FiniteHenselStepExistenceOver g omega p d j r := by
  intro hlift
  rcases finiteHenselOneStepExistenceProofOver_apply hproof hlift with
    ⟨_q, omegaNext, t, hliftNext, hrootStep, _hkill⟩
  exact ⟨omegaNext, t, hliftNext, hrootStep⟩

/-- Level-wise one-step proof gives the existing one-step existence interface. -/
theorem finiteHenselStepExistenceAtLevel_of_oneStepProofAtLevel
    {g p d j r : Nat}
    (hproof : FiniteHenselOneStepExistenceProofAtLevel g p d j r) :
    FiniteHenselStepExistenceAtLevel g p d j r := by
  intro omega
  exact finiteHenselStepExistenceOver_of_oneStepProofOver (hproof omega)

/-- All-level one-step proof gives the existing all-level one-step existence
interface. -/
theorem finiteHenselStepExistenceForAllLevels_of_oneStepProofForAllLevels
    {g p d j : Nat}
    (hproof : FiniteHenselOneStepExistenceProofForAllLevels g p d j) :
    FiniteHenselStepExistenceForAllLevels g p d j :=
  fun _r hr_pos =>
    finiteHenselStepExistenceAtLevel_of_oneStepProofAtLevel
      (finiteHenselOneStepExistenceProofForAllLevels_at hproof hr_pos)

end ApparitionDepth
