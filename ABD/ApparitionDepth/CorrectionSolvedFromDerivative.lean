/-
  ABD.ApparitionDepth.CorrectionSolvedFromDerivative

  Step 21O of the Apparition-Depth Decomposition project.

  This file connects derivative nonvanishing plus the linear-solve certificate to
  the concrete Hensel correction equation used in one finite Hensel step.
-/

import ABD.ApparitionDepth.ZModFieldLinearSolveProgress

namespace ApparitionDepth

/-! ## Correction equation solved from derivative nonvanishing -/

/-- Concrete correction-solve input at a representative `omega`.

This says: the derivative is nonzero, and the corresponding linear equations in
`ZMod p` can be solved. -/
def HenselCorrectionSolveInput (omega p d : Nat) : Prop :=
  HenselDerivativeNonzeroModP omega p d ∧
    HenselDerivativeZModLinearSolveCertificate omega p d

/-- Explicit-witness version of the correction-solve input. -/
def HenselCorrectionExplicitSolveInput (omega p d : Nat) : Prop :=
  HenselDerivativeNonzeroModP omega p d ∧
    HenselDerivativeZModLinearExplicitSolveAtNonzero omega p d

/-- Constructor for the concrete correction-solve input. -/
theorem henselCorrectionSolveInput_intro {omega p d : Nat}
    (hderiv : HenselDerivativeNonzeroModP omega p d)
    (hsolve : HenselDerivativeZModLinearSolveCertificate omega p d) :
    HenselCorrectionSolveInput omega p d :=
  ⟨hderiv, hsolve⟩

/-- Convert the explicit-witness version into the ordinary correction-solve input. -/
theorem henselCorrectionSolveInput_of_explicit {omega p d : Nat}
    (h : HenselCorrectionExplicitSolveInput omega p d) :
    HenselCorrectionSolveInput omega p d :=
  ⟨h.1, henselDerivativeZModLinearSolveCertificate_of_explicitAtNonzero h.2⟩

/-- Projection: derivative nonzero. -/
theorem henselCorrectionSolveInput_derivative {omega p d : Nat}
    (h : HenselCorrectionSolveInput omega p d) :
    HenselDerivativeNonzeroModP omega p d :=
  h.1

/-- Projection: linear-solve certificate. -/
theorem henselCorrectionSolveInput_linear {omega p d : Nat}
    (h : HenselCorrectionSolveInput omega p d) :
    HenselDerivativeZModLinearSolveCertificate omega p d :=
  h.2

/-- The correction equation is solved for every normalized quotient `q`. -/
theorem finiteHenselCorrectionSolved_of_solveInput
    {omega q p d : Nat}
    (h : HenselCorrectionSolveInput omega p d) :
    FiniteHenselCorrectionSolved omega q p d := by
  have hlin : FiniteHenselLinearSolved q p (branchDerivativeValue omega p d) :=
    correctionLinearSolved_of_zmodCertificate
      (henselCorrectionSolveInput_linear h)
      (henselCorrectionSolveInput_derivative h)
  exact hlin

/-- Extract correction-solution existence from the concrete solve input. -/
theorem finiteHenselCorrectionSolutionExists_of_solveInput
    {omega q p d : Nat}
    (h : HenselCorrectionSolveInput omega p d) :
    FiniteHenselCorrectionSolutionExists omega q p d :=
  finiteHenselCorrectionSolved_exists
    (finiteHenselCorrectionSolved_of_solveInput (q := q) h)

/-- Extract correction-solution uniqueness from the concrete solve input. -/
theorem finiteHenselCorrectionSolutionUnique_of_solveInput
    {omega q p d : Nat}
    (h : HenselCorrectionSolveInput omega p d) :
    FiniteHenselCorrectionSolutionUnique omega q p d :=
  finiteHenselCorrectionSolved_unique
    (finiteHenselCorrectionSolved_of_solveInput (q := q) h)

/-! ## Transport from branch-seed derivative data -/

/-- Branch-seed correction-solve input transported to a concrete representative. -/
def BranchSeedCorrectionSolveInput (g omega p d j : Nat) : Prop :=
  BranchSeedModP g omega p d j ∧
    BranchSeedDerivativeNonzeroModP g p d j ∧
      BranchSeedZModLinearSolveCertificate g p d j

/-- Constructor for branch-seed correction-solve input. -/
theorem branchSeedCorrectionSolveInput_intro {g omega p d j : Nat}
    (hseed : BranchSeedModP g omega p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hsolve : BranchSeedZModLinearSolveCertificate g p d j) :
    BranchSeedCorrectionSolveInput g omega p d j :=
  ⟨hseed, hderiv, hsolve⟩

/-- Branch-seed correction-solve input gives a solved branch-seed linear equation. -/
theorem branchSeedFiniteHenselLinearSolved_of_correctionInput
    {g omega q p d j : Nat}
    (h : BranchSeedCorrectionSolveInput g omega p d j) :
    BranchSeedFiniteHenselLinearSolved g q p d j :=
  branchSeedLinearSolved_of_zmodCertificate h.2.2 h.2.1

/-- Branch-seed derivative data transports derivative nonvanishing to the concrete
representative. -/
theorem henselDerivativeNonzero_of_branchSeedCorrectionSolveInput
    {g omega p d j : Nat}
    (h : BranchSeedCorrectionSolveInput g omega p d j) :
    HenselDerivativeNonzeroModP omega p d :=
  henselDerivativeNonzero_of_branchSeedDerivativeNonzero h.1 h.2.1

end ApparitionDepth
