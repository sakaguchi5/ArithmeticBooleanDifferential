/-
  ABD.ApparitionDepth.FiniteHenselStepUniqueness

  Step 21D-4 of the Apparition-Depth Decomposition project.

  This file packages one-step finite Hensel uniqueness and connects it to the
  already-built `HenselLiftUniqueAtLevel` interface.
-/

import ABD.ApparitionDepth.FiniteHenselStepExistence

namespace ApparitionDepth

/-! ## One-step uniqueness certificates -/

/-- Uniqueness of one-step lifts over a fixed old representative. -/
def FiniteHenselStepUniqueOver (g omega p d j r : Nat) : Prop :=
  ∀ omegaNext1 omegaNext2 t1 t2 : Nat,
    HenselBranchLiftAtLevel g omega p d j r →
    HenselBranchLiftAtLevel g omegaNext1 p d j (r + 1) →
    HenselBranchLiftAtLevel g omegaNext2 p d j (r + 1) →
    FiniteHenselRootStep omega omegaNext1 t1 p d r →
    FiniteHenselRootStep omega omegaNext2 t2 p d r →
      (omegaNext1 : ZMod (p ^ (r + 1))) =
        (omegaNext2 : ZMod (p ^ (r + 1)))

/-- Branch-level uniqueness at the next finite level. -/
def FiniteHenselStepUniqueAtLevel (g p d j r : Nat) : Prop :=
  HenselLiftUniqueAtLevel g p d j (r + 1)

/-- One-step uniqueness at every positive level. -/
def FiniteHenselStepUniqueForAllLevels (g p d j : Nat) : Prop :=
  ∀ r : Nat, 0 < r → FiniteHenselStepUniqueAtLevel g p d j r

/-- Constructor for uniqueness over a fixed old representative. -/
theorem finiteHenselStepUniqueOver_intro {g omega p d j r : Nat}
    (h : ∀ omegaNext1 omegaNext2 t1 t2 : Nat,
      HenselBranchLiftAtLevel g omega p d j r →
      HenselBranchLiftAtLevel g omegaNext1 p d j (r + 1) →
      HenselBranchLiftAtLevel g omegaNext2 p d j (r + 1) →
      FiniteHenselRootStep omega omegaNext1 t1 p d r →
      FiniteHenselRootStep omega omegaNext2 t2 p d r →
        (omegaNext1 : ZMod (p ^ (r + 1))) =
          (omegaNext2 : ZMod (p ^ (r + 1)))) :
    FiniteHenselStepUniqueOver g omega p d j r :=
  h

/-- Apply uniqueness over a fixed old representative. -/
theorem finiteHenselStepUniqueOver_apply
    {g omega omegaNext1 omegaNext2 t1 t2 p d j r : Nat}
    (huniq : FiniteHenselStepUniqueOver g omega p d j r)
    (hlift : HenselBranchLiftAtLevel g omega p d j r)
    (hlift1 : HenselBranchLiftAtLevel g omegaNext1 p d j (r + 1))
    (hlift2 : HenselBranchLiftAtLevel g omegaNext2 p d j (r + 1))
    (hstep1 : FiniteHenselRootStep omega omegaNext1 t1 p d r)
    (hstep2 : FiniteHenselRootStep omega omegaNext2 t2 p d r) :
    (omegaNext1 : ZMod (p ^ (r + 1))) =
      (omegaNext2 : ZMod (p ^ (r + 1))) :=
  huniq omegaNext1 omegaNext2 t1 t2 hlift hlift1 hlift2 hstep1 hstep2

/-- Constructor for branch-level next-level uniqueness. -/
theorem finiteHenselStepUniqueAtLevel_intro {g p d j r : Nat}
    (h : HenselLiftUniqueAtLevel g p d j (r + 1)) :
    FiniteHenselStepUniqueAtLevel g p d j r :=
  h

/-- Projection to the existing Hensel uniqueness interface. -/
theorem henselLiftUniqueAtLevel_succ_of_finiteHenselStepUniqueAtLevel
    {g p d j r : Nat}
    (h : FiniteHenselStepUniqueAtLevel g p d j r) :
    HenselLiftUniqueAtLevel g p d j (r + 1) :=
  h

/-- Extract a level from all-level one-step uniqueness. -/
theorem finiteHenselStepUniqueForAllLevels_at
    {g p d j r : Nat}
    (huniq : FiniteHenselStepUniqueForAllLevels g p d j)
    (hr_pos : 0 < r) :
    FiniteHenselStepUniqueAtLevel g p d j r :=
  huniq r hr_pos

/-- One-step uniqueness plus next-level existence gives next-level exists-unique. -/
theorem henselLiftExistsUnique_succ_of_stepExistence_stepUniqueness
    {g p d j r : Nat}
    (hexists : FiniteHenselStepExistenceAtLevel g p d j r)
    (huniq : FiniteHenselStepUniqueAtLevel g p d j r)
    (hlevel : HenselLiftExists g p d j r) :
    HenselLiftExistsUnique g p d j (r + 1) :=
  henselLiftExistsUnique_intro
    (henselLiftExists_succ_of_stepExistenceAtLevel hexists hlevel)
    (henselLiftUniqueAtLevel_succ_of_finiteHenselStepUniqueAtLevel huniq)

end ApparitionDepth
