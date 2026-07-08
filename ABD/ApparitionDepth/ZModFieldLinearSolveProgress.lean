/-
  ABD.ApparitionDepth.ZModFieldLinearSolveProgress

  Step 21N of the Apparition-Depth Decomposition project.

  This file pushes the linear-solve layer closer to an actual proof.  The only
  remaining field-specific point is represented by an explicit Nat witness for
  the correction digit.  Once such a witness is supplied, we build the existing
  `FiniteHenselLinearSolved` certificate used by the finite-Hensel pipeline.
-/

import ABD.ApparitionDepth.ZModFieldLinearSolve

namespace ApparitionDepth

/-! ## Explicit Nat-witness form of the linear solve -/

/-- An explicit solution witness for the linear equation

`q + t * a = 0` in `ZMod p`.

The witness is kept as a natural number because the surrounding Hensel pipeline
uses natural representatives for correction digits. -/
def ZModLinearSolutionWitness (q t p : Nat) (a : ZMod p) : Prop :=
  FiniteHenselLinearEquation q t p a

/-- An explicit uniqueness witness for solutions of `q + t * a = 0`. -/
def ZModLinearUniquenessWitness (q p : Nat) (a : ZMod p) : Prop :=
  FiniteHenselLinearSolutionUnique q p a

/-- The explicit Nat-witness version of a solved linear equation. -/
def ZModLinearExplicitSolved (q p : Nat) (a : ZMod p) : Prop :=
  ∃ t : Nat,
    ZModLinearSolutionWitness q t p a ∧
      ZModLinearUniquenessWitness q p a

/-- Constructor for an explicit linear solution witness. -/
theorem zmodLinearSolutionWitness_intro {q t p : Nat} {a : ZMod p}
    (h : FiniteHenselLinearEquation q t p a) :
    ZModLinearSolutionWitness q t p a :=
  h

/-- Projection from an explicit linear solution witness. -/
theorem zmodLinearSolutionWitness_eq {q t p : Nat} {a : ZMod p}
    (h : ZModLinearSolutionWitness q t p a) :
    FiniteHenselLinearEquation q t p a :=
  h

/-- Constructor for an explicit solved linear equation. -/
theorem zmodLinearExplicitSolved_intro {q t p : Nat} {a : ZMod p}
    (hsol : ZModLinearSolutionWitness q t p a)
    (huniq : ZModLinearUniquenessWitness q p a) :
    ZModLinearExplicitSolved q p a :=
  ⟨t, hsol, huniq⟩

/-- An explicit solved equation gives the existing `FiniteHenselLinearSolved`
interface. -/
theorem finiteHenselLinearSolved_of_explicitSolved {q p : Nat} {a : ZMod p}
    (h : ZModLinearExplicitSolved q p a) :
    FiniteHenselLinearSolved q p a := by
  rcases h with ⟨t, hsol, huniq⟩
  exact finiteHenselLinearSolved_intro
    (finiteHenselLinearSolutionExists_intro (zmodLinearSolutionWitness_eq hsol))
    huniq

/-- A nonzero coefficient is explicitly solvable if every right-hand side has an
explicit Nat witness.  This is the precise target for the later `ZMod p` field
proof using inverses. -/
def ZModLinearExplicitSolveAtNonzero (p : Nat) (a : ZMod p) : Prop :=
  a ≠ 0 → ∀ q : Nat, ZModLinearExplicitSolved q p a

/-- Convert the explicit nonzero solve target into the older certificate API. -/
theorem zmodLinearSolveCertificate_of_explicitAtNonzero {p : Nat} {a : ZMod p}
    (h : ZModLinearExplicitSolveAtNonzero p a) :
    ZModLinearSolveCertificate p a := by
  intro ha q
  exact finiteHenselLinearSolved_of_explicitSolved (h ha q)

/-- Branch-seed derivative version of the explicit nonzero solve target. -/
def BranchSeedZModLinearExplicitSolveAtNonzero (g p d j : Nat) : Prop :=
  ZModLinearExplicitSolveAtNonzero p (branchSeedDerivativeValue g p d j)

/-- Concrete derivative version of the explicit nonzero solve target. -/
def HenselDerivativeZModLinearExplicitSolveAtNonzero (omega p d : Nat) : Prop :=
  ZModLinearExplicitSolveAtNonzero p (branchDerivativeValue omega p d)

/-- Branch-seed explicit solve data gives the existing branch-seed certificate. -/
theorem branchSeedZModLinearSolveCertificate_of_explicitAtNonzero
    {g p d j : Nat}
    (h : BranchSeedZModLinearExplicitSolveAtNonzero g p d j) :
    BranchSeedZModLinearSolveCertificate g p d j :=
  zmodLinearSolveCertificate_of_explicitAtNonzero h

/-- Concrete derivative explicit solve data gives the existing concrete derivative
certificate. -/
theorem henselDerivativeZModLinearSolveCertificate_of_explicitAtNonzero
    {omega p d : Nat}
    (h : HenselDerivativeZModLinearExplicitSolveAtNonzero omega p d) :
    HenselDerivativeZModLinearSolveCertificate omega p d :=
  zmodLinearSolveCertificate_of_explicitAtNonzero h

end ApparitionDepth
