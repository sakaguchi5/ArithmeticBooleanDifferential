/-
  ABD.ApparitionDepth.FiniteHenselLinearEquation

  Step 21D-2 of the Apparition-Depth Decomposition project.

  This file names the linear congruence that appears in one finite Hensel step.
  The intended equation is

      q + t * f'(omega) = 0 mod p.

  Solving this equation is the local algebraic core of the Hensel step.
-/

import ABD.ApparitionDepth.FiniteHenselStep

namespace ApparitionDepth

/-! ## Linear equation for the Hensel correction -/

/-- The finite Hensel linear equation

`q + t * deriv = 0` in `ZMod p`.

Here `q` is the normalized error term and `deriv` is the derivative value in
`ZMod p`. -/
def FiniteHenselLinearEquation (q t p : Nat) (deriv : ZMod p) : Prop :=
  (q : ZMod p) + (t : ZMod p) * deriv = 0

/-- Existence of a correction solving the finite Hensel linear equation. -/
def FiniteHenselLinearSolutionExists (q p : Nat) (deriv : ZMod p) : Prop :=
  ∃ t : Nat, FiniteHenselLinearEquation q t p deriv

/-- Uniqueness of the correction modulo `p`. -/
def FiniteHenselLinearSolutionUnique (q p : Nat) (deriv : ZMod p) : Prop :=
  ∀ t1 t2 : Nat,
    FiniteHenselLinearEquation q t1 p deriv →
    FiniteHenselLinearEquation q t2 p deriv →
      (t1 : ZMod p) = (t2 : ZMod p)

/-- Existence and uniqueness of the Hensel linear correction. -/
def FiniteHenselLinearSolved (q p : Nat) (deriv : ZMod p) : Prop :=
  FiniteHenselLinearSolutionExists q p deriv ∧
    FiniteHenselLinearSolutionUnique q p deriv

/-- Constructor for the linear equation. -/
theorem finiteHenselLinearEquation_intro {q t p : Nat} {deriv : ZMod p}
    (h : (q : ZMod p) + (t : ZMod p) * deriv = 0) :
    FiniteHenselLinearEquation q t p deriv :=
  h

/-- Projection from the linear equation. -/
theorem finiteHenselLinearEquation_eq {q t p : Nat} {deriv : ZMod p}
    (h : FiniteHenselLinearEquation q t p deriv) :
    (q : ZMod p) + (t : ZMod p) * deriv = 0 :=
  h

/-- Constructor for existence of a linear solution. -/
theorem finiteHenselLinearSolutionExists_intro {q t p : Nat} {deriv : ZMod p}
    (h : FiniteHenselLinearEquation q t p deriv) :
    FiniteHenselLinearSolutionExists q p deriv :=
  ⟨t, h⟩

/-- Extract a witness from solution existence. -/
theorem finiteHenselLinearSolutionExists_witness {q p : Nat} {deriv : ZMod p}
    (h : FiniteHenselLinearSolutionExists q p deriv) :
    ∃ t : Nat, FiniteHenselLinearEquation q t p deriv :=
  h

/-- Constructor for solution uniqueness. -/
theorem finiteHenselLinearSolutionUnique_intro {q p : Nat} {deriv : ZMod p}
    (h : ∀ t1 t2 : Nat,
      FiniteHenselLinearEquation q t1 p deriv →
      FiniteHenselLinearEquation q t2 p deriv →
        (t1 : ZMod p) = (t2 : ZMod p)) :
    FiniteHenselLinearSolutionUnique q p deriv :=
  h

/-- Apply solution uniqueness. -/
theorem finiteHenselLinearSolutionUnique_apply {q t1 t2 p : Nat} {deriv : ZMod p}
    (huniq : FiniteHenselLinearSolutionUnique q p deriv)
    (h1 : FiniteHenselLinearEquation q t1 p deriv)
    (h2 : FiniteHenselLinearEquation q t2 p deriv) :
    (t1 : ZMod p) = (t2 : ZMod p) :=
  huniq t1 t2 h1 h2

/-- Constructor for existence plus uniqueness. -/
theorem finiteHenselLinearSolved_intro {q p : Nat} {deriv : ZMod p}
    (hexists : FiniteHenselLinearSolutionExists q p deriv)
    (huniq : FiniteHenselLinearSolutionUnique q p deriv) :
    FiniteHenselLinearSolved q p deriv :=
  ⟨hexists, huniq⟩

/-- Projection: existence from solved linear equation. -/
theorem finiteHenselLinearSolved_exists {q p : Nat} {deriv : ZMod p}
    (h : FiniteHenselLinearSolved q p deriv) :
    FiniteHenselLinearSolutionExists q p deriv :=
  h.1

/-- Projection: uniqueness from solved linear equation. -/
theorem finiteHenselLinearSolved_unique {q p : Nat} {deriv : ZMod p}
    (h : FiniteHenselLinearSolved q p deriv) :
    FiniteHenselLinearSolutionUnique q p deriv :=
  h.2

/-- Branch derivative version of the linear equation. -/
def BranchSeedFiniteHenselLinearEquation (g q t p d j : Nat) : Prop :=
  FiniteHenselLinearEquation q t p (branchSeedDerivativeValue g p d j)

/-- Branch derivative version of linear solved data. -/
def BranchSeedFiniteHenselLinearSolved (g q p d j : Nat) : Prop :=
  FiniteHenselLinearSolved q p (branchSeedDerivativeValue g p d j)

/-- Constructor for the branch derivative linear equation. -/
theorem branchSeedFiniteHenselLinearEquation_intro {g q t p d j : Nat}
    (h : FiniteHenselLinearEquation q t p (branchSeedDerivativeValue g p d j)) :
    BranchSeedFiniteHenselLinearEquation g q t p d j :=
  h

/-- Projection from the branch derivative linear equation. -/
theorem branchSeedFiniteHenselLinearEquation_eq {g q t p d j : Nat}
    (h : BranchSeedFiniteHenselLinearEquation g q t p d j) :
    FiniteHenselLinearEquation q t p (branchSeedDerivativeValue g p d j) :=
  h

end ApparitionDepth
