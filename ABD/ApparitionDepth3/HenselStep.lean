/-
  ABD.ApparitionDepth3.HenselStep

  Second layer of the organic Hensel block.

  This file packages the local one-step Hensel data.  Unlike the earlier
  temporary version, it contains no placeholder.  The bridge from simple-root language
  to the kernel now requires explicit `HenselLocalData`, whose components are the
  natural local lemmas: descent, base level, one-step existence, and one-step
  uniqueness.
-/

import ABD.ApparitionDepth3.HenselLocal

namespace ApparitionDepth3

/-- The local finite-Hensel kernel.

This is the minimal local data required to run finite Hensel induction. -/
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

/-- The seed itself gives the level-one lift of a simple root. -/
theorem baseLiftAtLevel_one_of_simpleRoot
    {seed p d : Nat}
    (hsimple : SimpleRootModP seed p d) :
    LiftAtLevel seed seed p d 1 :=
  ⟨rfl, simpleRoot_root hsimple⟩

/-- Level-one uniqueness is just equality of representatives congruent to the
same seed modulo `p`. -/
theorem baseUniqueAtLevel_one_of_seedCongr
    {seed p d : Nat} :
    ∀ omega₁ omega₂ : Nat,
      LiftAtLevel seed omega₁ p d 1 →
      LiftAtLevel seed omega₂ p d 1 →
        (omega₁ : ZMod (p ^ 1)) = (omega₂ : ZMod (p ^ 1)) := by
  intro omega₁ omega₂ h₁ h₂
  have hmod : (omega₁ : ZMod p) = (omega₂ : ZMod p) :=
    h₁.1.trans h₂.1.symm
  rw [levelOneModulus_eq p]
  exact hmod

/-- Assemble the finite-Hensel kernel from a simple root and local mathematical
data.

The base level is proved here from the simple root.  The only remaining local
input is the genuine one-step Hensel algebra. -/
theorem finiteHenselKernel_of_localData
    {seed p d : Nat}
    (hsimple : SimpleRootModP seed p d)
    (hlocal : HenselLocalData seed p d) :
    FiniteHenselKernel seed p d where
  root_descend := hlocal.descent
  base_exists := ⟨seed, baseLiftAtLevel_one_of_simpleRoot hsimple⟩
  base_unique := baseUniqueAtLevel_one_of_seedCongr
  step_exists := hlocal.step_exists
  step_unique := hlocal.step_unique

/-- Simple-root spelling of the kernel assembly.

The external theorem placeholder is gone.  A caller must now supply the natural local Hensel
step lemmas as `HenselLocalData`; future concrete files should prove that data
from quotient/correction/expansion arguments. -/
theorem finiteHenselKernel_of_simpleRoot
    {seed p d : Nat}
    (hsimple : SimpleRootModP seed p d)
    (hlocal : HenselLocalData seed p d) :
    FiniteHenselKernel seed p d :=
  finiteHenselKernel_of_localData hsimple hlocal

/-- Seed-simple-root spelling of the finite Hensel kernel assembly. -/
theorem finiteHenselKernel_of_seedSimpleRoot
    {seed p d : Nat}
    (hsimple : SeedSimpleRootModP seed p d)
    (hlocal : HenselLocalData seed p d) :
    FiniteHenselKernel seed p d :=
  finiteHenselKernel_of_simpleRoot hsimple hlocal

end ApparitionDepth3
