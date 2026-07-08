/-
  ABD.ApparitionDepth.LinearCorrectionSolve

  Step 21E-4 of the Apparition-Depth Decomposition project.

  This file packages the solution of the local linear correction equation and
  records the certificate that the chosen correction actually kills the next-level
  error.
-/

import ABD.ApparitionDepth.HenselQuotient

namespace ApparitionDepth

/-! ## Solving the correction equation for one step -/

/-- The linear correction equation attached to an old representative `omega` and
its normalized error quotient `q`:

`q + t * (d*omega^(d-1)) = 0` in `ZMod p`. -/
def FiniteHenselCorrectionEquation (omega q t p d : Nat) : Prop :=
  FiniteHenselLinearEquation q t p (branchDerivativeValue omega p d)

/-- The correction equation has a solution. -/
def FiniteHenselCorrectionSolutionExists (omega q p d : Nat) : Prop :=
  ∃ t : Nat, FiniteHenselCorrectionEquation omega q t p d

/-- The correction equation has a unique solution modulo `p`. -/
def FiniteHenselCorrectionSolutionUnique (omega q p d : Nat) : Prop :=
  ∀ t1 t2 : Nat,
    FiniteHenselCorrectionEquation omega q t1 p d →
    FiniteHenselCorrectionEquation omega q t2 p d →
      (t1 : ZMod p) = (t2 : ZMod p)

/-- The correction equation is solved. -/
def FiniteHenselCorrectionSolved (omega q p d : Nat) : Prop :=
  FiniteHenselCorrectionSolutionExists omega q p d ∧
    FiniteHenselCorrectionSolutionUnique omega q p d

/-- Constructor for the correction equation. -/
theorem finiteHenselCorrectionEquation_intro {omega q t p d : Nat}
    (h : FiniteHenselLinearEquation q t p (branchDerivativeValue omega p d)) :
    FiniteHenselCorrectionEquation omega q t p d :=
  h

/-- Projection from the correction equation. -/
theorem finiteHenselCorrectionEquation_linear {omega q t p d : Nat}
    (h : FiniteHenselCorrectionEquation omega q t p d) :
    FiniteHenselLinearEquation q t p (branchDerivativeValue omega p d) :=
  h

/-- Constructor for correction-solution existence. -/
theorem finiteHenselCorrectionSolutionExists_intro {omega q t p d : Nat}
    (h : FiniteHenselCorrectionEquation omega q t p d) :
    FiniteHenselCorrectionSolutionExists omega q p d :=
  ⟨t, h⟩

/-- Extract a correction-solution witness. -/
theorem finiteHenselCorrectionSolutionExists_witness {omega q p d : Nat}
    (h : FiniteHenselCorrectionSolutionExists omega q p d) :
    ∃ t : Nat, FiniteHenselCorrectionEquation omega q t p d :=
  h

/-- Constructor for correction-solution uniqueness. -/
theorem finiteHenselCorrectionSolutionUnique_intro {omega q p d : Nat}
    (h : ∀ t1 t2 : Nat,
      FiniteHenselCorrectionEquation omega q t1 p d →
      FiniteHenselCorrectionEquation omega q t2 p d →
        (t1 : ZMod p) = (t2 : ZMod p)) :
    FiniteHenselCorrectionSolutionUnique omega q p d :=
  h

/-- Apply correction-solution uniqueness. -/
theorem finiteHenselCorrectionSolutionUnique_apply
    {omega q t1 t2 p d : Nat}
    (huniq : FiniteHenselCorrectionSolutionUnique omega q p d)
    (h1 : FiniteHenselCorrectionEquation omega q t1 p d)
    (h2 : FiniteHenselCorrectionEquation omega q t2 p d) :
    (t1 : ZMod p) = (t2 : ZMod p) :=
  huniq t1 t2 h1 h2

/-- Constructor for solved correction equation. -/
theorem finiteHenselCorrectionSolved_intro {omega q p d : Nat}
    (hexists : FiniteHenselCorrectionSolutionExists omega q p d)
    (huniq : FiniteHenselCorrectionSolutionUnique omega q p d) :
    FiniteHenselCorrectionSolved omega q p d :=
  ⟨hexists, huniq⟩

/-- Projection: existence from a solved correction. -/
theorem finiteHenselCorrectionSolved_exists {omega q p d : Nat}
    (h : FiniteHenselCorrectionSolved omega q p d) :
    FiniteHenselCorrectionSolutionExists omega q p d :=
  h.1

/-- Projection: uniqueness from a solved correction. -/
theorem finiteHenselCorrectionSolved_unique {omega q p d : Nat}
    (h : FiniteHenselCorrectionSolved omega q p d) :
    FiniteHenselCorrectionSolutionUnique omega q p d :=
  h.2

/-- A local certificate that the chosen correction digit, together with quotient
and binomial truncation data, really produces a root at level `r+1`.

The final conjunct is the root conclusion.  It is separated out so that the later
binomial calculation can replace this certificate by an actual proof. -/
def FiniteHenselCorrectionKillsError
    (omega omegaNext q t p d r : Nat) : Prop :=
  FiniteHenselErrorQuotient omega q p d r ∧
    FiniteHenselBinomialTruncation omega omegaNext t p d r ∧
      FiniteHenselCorrectionEquation omega q t p d ∧
        OmegaRootAtLevel omegaNext p d (r + 1)

/-- Constructor for the error-killing correction certificate. -/
theorem finiteHenselCorrectionKillsError_intro
    {omega omegaNext q t p d r : Nat}
    (hquot : FiniteHenselErrorQuotient omega q p d r)
    (htrunc : FiniteHenselBinomialTruncation omega omegaNext t p d r)
    (hlin : FiniteHenselCorrectionEquation omega q t p d)
    (hrootNext : OmegaRootAtLevel omegaNext p d (r + 1)) :
    FiniteHenselCorrectionKillsError omega omegaNext q t p d r :=
  ⟨hquot, htrunc, hlin, hrootNext⟩

/-- Projection: normalized quotient. -/
theorem finiteHenselCorrectionKillsError_quotient
    {omega omegaNext q t p d r : Nat}
    (h : FiniteHenselCorrectionKillsError omega omegaNext q t p d r) :
    FiniteHenselErrorQuotient omega q p d r :=
  h.1

/-- Projection: binomial truncation. -/
theorem finiteHenselCorrectionKillsError_truncation
    {omega omegaNext q t p d r : Nat}
    (h : FiniteHenselCorrectionKillsError omega omegaNext q t p d r) :
    FiniteHenselBinomialTruncation omega omegaNext t p d r :=
  h.2.1

/-- Projection: linear equation. -/
theorem finiteHenselCorrectionKillsError_linear
    {omega omegaNext q t p d r : Nat}
    (h : FiniteHenselCorrectionKillsError omega omegaNext q t p d r) :
    FiniteHenselCorrectionEquation omega q t p d :=
  h.2.2.1

/-- Projection: next-level root. -/
theorem finiteHenselCorrectionKillsError_rootNext
    {omega omegaNext q t p d r : Nat}
    (h : FiniteHenselCorrectionKillsError omega omegaNext q t p d r) :
    OmegaRootAtLevel omegaNext p d (r + 1) :=
  h.2.2.2

end ApparitionDepth
