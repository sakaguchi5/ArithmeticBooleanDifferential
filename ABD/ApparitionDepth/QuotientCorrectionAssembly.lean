/-
  ABD.ApparitionDepth.QuotientCorrectionAssembly

  Step 21P of the Apparition-Depth Decomposition project.

  This file tightens the one-step existence side: quotient data plus a solved
  correction equation plus binomial truncation is packaged into the existing
  `FiniteHenselCorrectionKillsError` object.
-/

import ABD.ApparitionDepth.OneStepExistenceActual
import ABD.ApparitionDepth.CorrectionSolvedFromDerivative

namespace ApparitionDepth

/-! ## Assembling quotient, truncation, and correction data -/

/-- A focused local assembly input for one Hensel correction. -/
def FiniteHenselCorrectionAssemblyInput
    (omega omegaNext q t p d r : Nat) : Prop :=
  FiniteHenselErrorQuotient omega q p d r ∧
    FiniteHenselBinomialTruncation omega omegaNext t p d r ∧
      FiniteHenselCorrectionEquation omega q t p d ∧
        OmegaRootAtLevel omegaNext p d (r + 1)

/-- Constructor for the focused assembly input. -/
theorem finiteHenselCorrectionAssemblyInput_intro
    {omega omegaNext q t p d r : Nat}
    (hquot : FiniteHenselErrorQuotient omega q p d r)
    (htrunc : FiniteHenselBinomialTruncation omega omegaNext t p d r)
    (hlin : FiniteHenselCorrectionEquation omega q t p d)
    (hrootNext : OmegaRootAtLevel omegaNext p d (r + 1)) :
    FiniteHenselCorrectionAssemblyInput omega omegaNext q t p d r :=
  ⟨hquot, htrunc, hlin, hrootNext⟩

/-- The focused assembly input is exactly the existing error-killing certificate. -/
theorem finiteHenselCorrectionKillsError_of_assemblyInput
    {omega omegaNext q t p d r : Nat}
    (h : FiniteHenselCorrectionAssemblyInput omega omegaNext q t p d r) :
    FiniteHenselCorrectionKillsError omega omegaNext q t p d r :=
  finiteHenselCorrectionKillsError_intro h.1 h.2.1 h.2.2.1 h.2.2.2

/-- A correction solution together with quotient/truncation/root data gives the
existing error-killing certificate. -/
theorem finiteHenselCorrectionKillsError_of_solution
    {omega omegaNext q t p d r : Nat}
    (hquot : FiniteHenselErrorQuotient omega q p d r)
    (htrunc : FiniteHenselBinomialTruncation omega omegaNext t p d r)
    (hsol : FiniteHenselCorrectionEquation omega q t p d)
    (hrootNext : OmegaRootAtLevel omegaNext p d (r + 1)) :
    FiniteHenselCorrectionKillsError omega omegaNext q t p d r :=
  finiteHenselCorrectionKillsError_of_assemblyInput
    (finiteHenselCorrectionAssemblyInput_intro hquot htrunc hsol hrootNext)

/-- A solved correction equation provides some correction digit.  This is the
local extraction used by future one-step existence proofs. -/
theorem exists_correctionDigit_of_solveInput
    {omega q p d : Nat}
    (hsolve : HenselCorrectionSolveInput omega p d) :
    ∃ t : Nat, FiniteHenselCorrectionEquation omega q t p d :=
  finiteHenselCorrectionSolutionExists_witness
    (finiteHenselCorrectionSolutionExists_of_solveInput (q := q) hsolve)

/-- One-step existence can be reduced to supplying the candidate next lift and the
proof that the chosen correction kills the error. -/
def FiniteHenselOneStepExistenceAssemblyOver
    (g omega p d j r : Nat) : Prop :=
  HenselBranchLiftAtLevel g omega p d j r →
    ∃ q omegaNext t : Nat,
      HenselBranchLiftAtLevel g omegaNext p d j (r + 1) ∧
        FiniteHenselRootStep omega omegaNext t p d r ∧
          FiniteHenselCorrectionAssemblyInput omega omegaNext q t p d r

/-- The assembly version gives the existing actual one-step existence package. -/
theorem finiteHenselOneStepExistenceActualOver_of_assembly
    {g omega p d j r : Nat}
    (h : FiniteHenselOneStepExistenceAssemblyOver g omega p d j r) :
    FiniteHenselOneStepExistenceActualOver g omega p d j r := by
  intro hlift
  rcases h hlift with ⟨q, omegaNext, t, hliftNext, hrootStep, hasm⟩
  exact ⟨q, omegaNext, t, hliftNext, hrootStep,
    finiteHenselCorrectionKillsError_of_assemblyInput hasm⟩

end ApparitionDepth
