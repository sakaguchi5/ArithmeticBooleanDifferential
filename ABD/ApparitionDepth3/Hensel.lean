/-
  ABD.ApparitionDepth3.Hensel

  Organic finite-Hensel spine.

  This is the replacement for the old many-file Hensel interface/final split.
  The local algebra is represented by one compact kernel:
    * roots descend one precision;
    * level-one existence and uniqueness;
    * one-step existence;
    * one-step uniqueness above a fixed old lift.

  From this kernel we prove the finite induction theorem once, directly.
-/

import ABD.ApparitionDepth3.SimpleRoot

namespace ApparitionDepth3

/-- A lift at precision `p^r` staying on the same seed modulo `p`. -/
def LiftAtLevel (seed omega p d r : Nat) : Prop :=
  BranchSeedModP seed omega p ∧ RootAtLevel omega p d r

/-- Existence and uniqueness of a seed-compatible lift at level `r`. -/
def ExistsUniqueLiftAtLevel (seed p d r : Nat) : Prop :=
  ∃ omega : Nat,
    LiftAtLevel seed omega p d r ∧
      ∀ omega' : Nat,
        LiftAtLevel seed omega' p d r →
          (omega' : ZMod (p ^ r)) = (omega : ZMod (p ^ r))

/-- The local finite-Hensel kernel.

This is intentionally a single object, not a chain of bridge files.  It is the
minimal local data required to run finite Hensel induction. -/
structure FiniteHenselKernel (seed p d : Nat) : Prop where
  root_descend : ∀ {x r : Nat}, 0 < r →
    RootAtLevel x p d (r + 1) → RootAtLevel x p d r
  base_exists : ∃ omega : Nat, LiftAtLevel seed omega p d 1
  base_unique : ∀ omega₁ omega₂ : Nat,
    LiftAtLevel seed omega₁ p d 1 →
    LiftAtLevel seed omega₂ p d 1 →
      (omega₁ : ZMod (p ^ 1)) = (omega₂ : ZMod (p ^ 1))
  step_exists : ∀ r : Nat, 0 < r → ∀ omega : Nat,
    LiftAtLevel seed omega p d r →
      ∃ omegaNext : Nat,
        LiftAtLevel seed omegaNext p d (r + 1) ∧
          (omegaNext : ZMod (p ^ r)) = (omega : ZMod (p ^ r))
  step_unique : ∀ r : Nat, 0 < r → ∀ omega omegaNext₁ omegaNext₂ : Nat,
    LiftAtLevel seed omega p d r →
    LiftAtLevel seed omegaNext₁ p d (r + 1) →
    (omegaNext₁ : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) →
    LiftAtLevel seed omegaNext₂ p d (r + 1) →
    (omegaNext₂ : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) →
      (omegaNext₁ : ZMod (p ^ (r + 1))) =
        (omegaNext₂ : ZMod (p ^ (r + 1)))

/-- A level `r+1` lift descends to a level `r` lift. -/
theorem liftAtLevel_descend {seed omega p d r : Nat}
    (hkernel : FiniteHenselKernel seed p d)
    (hr_pos : 0 < r)
    (hlift : LiftAtLevel seed omega p d (r + 1)) :
    LiftAtLevel seed omega p d r :=
  ⟨hlift.1, hkernel.root_descend hr_pos hlift.2⟩

/-- Level one exists-unique from the kernel. -/
theorem existsUniqueLiftAtLevel_one_of_kernel {seed p d : Nat}
    (hkernel : FiniteHenselKernel seed p d) :
    ExistsUniqueLiftAtLevel seed p d 1 := by
  rcases hkernel.base_exists with ⟨omega, homega⟩
  refine ⟨omega, homega, ?_⟩
  intro omega' homega'
  exact hkernel.base_unique omega' omega homega' homega

/-- Finite Hensel induction: the kernel produces a unique lift at every positive
precision. -/
theorem existsUniqueLiftAtLevel_of_kernel {seed p d r : Nat}
    (hkernel : FiniteHenselKernel seed p d)
    (hr_pos : 0 < r) :
    ExistsUniqueLiftAtLevel seed p d r := by
  revert hr_pos
  induction r with
  | zero =>
      intro hr_pos
      exact False.elim ((Nat.not_lt_zero 0) hr_pos)
  | succ n ih =>
      intro _hpos
      cases n with
      | zero =>
          simpa using existsUniqueLiftAtLevel_one_of_kernel hkernel
      | succ k =>
          have hk_pos : 0 < k + 1 := Nat.succ_pos k
          have hprev : ExistsUniqueLiftAtLevel seed p d (k + 1) := ih hk_pos
          rcases hprev with ⟨omega, homega, huniqOld⟩
          rcases hkernel.step_exists (k + 1) hk_pos omega homega with
            ⟨omegaNext, hnext, hreduce⟩
          refine ⟨omegaNext, hnext, ?_⟩
          intro omegaNext' hnext'
          have hdown : LiftAtLevel seed omegaNext' p d (k + 1) :=
            liftAtLevel_descend hkernel hk_pos hnext'
          have hreduce' :
              (omegaNext' : ZMod (p ^ (k + 1))) =
                (omega : ZMod (p ^ (k + 1))) :=
            huniqOld omegaNext' hdown
          exact hkernel.step_unique (k + 1) hk_pos omega omegaNext' omegaNext
            homega hnext' hreduce' hnext hreduce

/-- Extract a root at level from the finite-Hensel theorem. -/
theorem rootAtLevel_of_kernel {seed p d r : Nat}
    (hkernel : FiniteHenselKernel seed p d)
    (hr_pos : 0 < r) :
    ∃ omega : Nat, RootAtLevel omega p d r := by
  rcases existsUniqueLiftAtLevel_of_kernel hkernel hr_pos with
    ⟨omega, hlift, _huniq⟩
  exact ⟨omega, hlift.2⟩

end ApparitionDepth3
