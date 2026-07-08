/-
  ABD.ApparitionDepth3.HenselStep

  Second layer of the organic Hensel block.

  This file packages the local one-step Hensel data.  The package is intentionally
  one mathematical object instead of the old interface/final/actual chain:
    * roots descend one precision;
    * the seed-compatible root exists and is unique at level 1;
    * every lift at level r has a compatible lift at level r+1;
    * that one-step lift is unique above the chosen old lift.

  Later, the real local algebra theorem should prove this kernel from
  `SimpleRootModP seed p d`.  For now this is the exact reusable Hensel kernel
  needed by the finite induction theorem.
-/

import ABD.ApparitionDepth3.HenselAlgebra

namespace ApparitionDepth3

/-- The local finite-Hensel kernel.

This is the minimal local data required to run finite Hensel induction.  It is
where the future one-step proof from a simple root will plug in. -/
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

end ApparitionDepth3
