/-
  ABD.ApparitionDepth.FiniteHenselStep

  Step 21D-1 of the Apparition-Depth Decomposition project.

  This file introduces the finite one-step Hensel-lift relation.  The actual
  binomial expansion proof is intentionally not placed here; this file only names
  the step data that later finite-Hensel proofs must construct.
-/

import ABD.ApparitionDepth.HenselLemmaMathlibBridge

namespace ApparitionDepth

/-! ## One-step finite Hensel lift relation -/

/-- `omegaNext` is obtained from `omega` by a one-step correction `t * p^r`,
viewed at the next precision `p^(r+1)`, and it reduces back to `omega` modulo
`p^r`.

This is the finite-level shape of

`omega_{r+1} = omega_r + t * p^r`.
-/
def FiniteHenselStepRelation (omega omegaNext t p r : Nat) : Prop :=
  (omegaNext : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) ∧
    (omegaNext : ZMod (p ^ (r + 1))) =
      (omega : ZMod (p ^ (r + 1))) +
        (t : ZMod (p ^ (r + 1))) * (p ^ r : ZMod (p ^ (r + 1)))

/-- A one-step Hensel root step for `X^d - 1`: the old representative is a root
at level `r`, the new representative is a root at level `r+1`, and the two are
connected by a one-step correction. -/
def FiniteHenselRootStep (omega omegaNext t p d r : Nat) : Prop :=
  FiniteHenselStepRelation omega omegaNext t p r ∧
    OmegaRootAtLevel omega p d r ∧
      OmegaRootAtLevel omegaNext p d (r + 1)

/-- Constructor for `FiniteHenselStepRelation`. -/
theorem finiteHenselStepRelation_intro {omega omegaNext t p r : Nat}
    (hreduce : (omegaNext : ZMod (p ^ r)) = (omega : ZMod (p ^ r)))
    (hformula : (omegaNext : ZMod (p ^ (r + 1))) =
      (omega : ZMod (p ^ (r + 1))) +
        (t : ZMod (p ^ (r + 1))) * (p ^ r : ZMod (p ^ (r + 1)))) :
    FiniteHenselStepRelation omega omegaNext t p r :=
  ⟨hreduce, hformula⟩

/-- Projection: reduction to the previous level. -/
theorem finiteHenselStepRelation_reduce {omega omegaNext t p r : Nat}
    (h : FiniteHenselStepRelation omega omegaNext t p r) :
    (omegaNext : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) :=
  h.1

/-- Projection: correction formula at the next level. -/
theorem finiteHenselStepRelation_formula {omega omegaNext t p r : Nat}
    (h : FiniteHenselStepRelation omega omegaNext t p r) :
    (omegaNext : ZMod (p ^ (r + 1))) =
      (omega : ZMod (p ^ (r + 1))) +
        (t : ZMod (p ^ (r + 1))) * (p ^ r : ZMod (p ^ (r + 1))) :=
  h.2

/-- Constructor for `FiniteHenselRootStep`. -/
theorem finiteHenselRootStep_intro {omega omegaNext t p d r : Nat}
    (hstep : FiniteHenselStepRelation omega omegaNext t p r)
    (hroot : OmegaRootAtLevel omega p d r)
    (hrootNext : OmegaRootAtLevel omegaNext p d (r + 1)) :
    FiniteHenselRootStep omega omegaNext t p d r :=
  ⟨hstep, hroot, hrootNext⟩

/-- Projection: the step relation. -/
theorem finiteHenselRootStep_step {omega omegaNext t p d r : Nat}
    (h : FiniteHenselRootStep omega omegaNext t p d r) :
    FiniteHenselStepRelation omega omegaNext t p r :=
  h.1

/-- Projection: old root condition. -/
theorem finiteHenselRootStep_root {omega omegaNext t p d r : Nat}
    (h : FiniteHenselRootStep omega omegaNext t p d r) :
    OmegaRootAtLevel omega p d r :=
  h.2.1

/-- Projection: lifted root condition. -/
theorem finiteHenselRootStep_rootNext {omega omegaNext t p d r : Nat}
    (h : FiniteHenselRootStep omega omegaNext t p d r) :
    OmegaRootAtLevel omegaNext p d (r + 1) :=
  h.2.2

/-- Projection: reduction to the previous level from a root step. -/
theorem finiteHenselRootStep_reduce {omega omegaNext t p d r : Nat}
    (h : FiniteHenselRootStep omega omegaNext t p d r) :
    (omegaNext : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) :=
  finiteHenselStepRelation_reduce (finiteHenselRootStep_step h)

/-- Projection: correction formula from a root step. -/
theorem finiteHenselRootStep_formula {omega omegaNext t p d r : Nat}
    (h : FiniteHenselRootStep omega omegaNext t p d r) :
    (omegaNext : ZMod (p ^ (r + 1))) =
      (omega : ZMod (p ^ (r + 1))) +
        (t : ZMod (p ^ (r + 1))) * (p ^ r : ZMod (p ^ (r + 1))) :=
  finiteHenselStepRelation_formula (finiteHenselRootStep_step h)

end ApparitionDepth
