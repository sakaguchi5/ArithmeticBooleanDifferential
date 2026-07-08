/-
  ABD.ApparitionDepth.BranchDerivativeUnit

  Step 21H of the Apparition-Depth Decomposition project.

  This file connects derivative nonvanishing to solved correction equations.  The
  field-theoretic part is supplied by the `ZModLinearSolveCertificate` introduced
  in Step 21G.
-/

import ABD.ApparitionDepth.ZModFieldLinearSolve

namespace ApparitionDepth

/-! ## Solved correction equations from derivative nonvanishing -/

/-- For a concrete representative `omega`, every normalized error quotient has a
solved correction equation. -/
def HenselCorrectionSolvedForAllErrors (omega p d : Nat) : Prop :=
  ∀ q : Nat, FiniteHenselCorrectionSolved omega q p d

/-- Branch-seed version: every normalized error quotient has a solved correction
for the representative `omega` of the branch seed. -/
def BranchSeedCorrectionSolvedForAllErrors
    (_g omega p d _j : Nat) : Prop :=
  ∀ q : Nat, FiniteHenselCorrectionSolved omega q p d

/-- Convert a solved linear equation into a solved correction equation. -/
theorem finiteHenselCorrectionSolved_of_linearSolved
    {omega q p d : Nat}
    (h : FiniteHenselLinearSolved q p (branchDerivativeValue omega p d)) :
    FiniteHenselCorrectionSolved omega q p d :=
  h

/-- A concrete derivative linear-solve certificate plus derivative nonvanishing
solves every correction equation for that representative. -/
theorem henselCorrectionSolvedForAllErrors_of_zmodCertificate
    {omega p d : Nat}
    (hcert : HenselDerivativeZModLinearSolveCertificate omega p d)
    (hderiv : HenselDerivativeNonzeroModP omega p d) :
    HenselCorrectionSolvedForAllErrors omega p d := by
  intro q
  exact finiteHenselCorrectionSolved_of_linearSolved
    (correctionLinearSolved_of_zmodCertificate (q := q) hcert hderiv)

/-- Branch-seed data transports derivative nonvanishing to `omega`, and then the
linear-solve certificate gives solved correction equations. -/
theorem branchSeedCorrectionSolvedForAllErrors_of_zmodCertificate
    {g omega p d j : Nat}
    (hseed : BranchSeedModP g omega p d j)
    (hcert : HenselDerivativeZModLinearSolveCertificate omega p d)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    BranchSeedCorrectionSolvedForAllErrors g omega p d j :=
  henselCorrectionSolvedForAllErrors_of_zmodCertificate hcert
    (henselDerivativeNonzero_of_branchSeedDerivativeNonzero hseed hderiv)

/-- If a branch-seed derivative factor certificate is available, it supplies the
compressed derivative nonzero condition and hence solved correction equations. -/
theorem branchSeedCorrectionSolvedForAllErrors_of_factorCertificate
    {g omega p d j : Nat}
    (hseed : BranchSeedModP g omega p d j)
    (hcertSolve : HenselDerivativeZModLinearSolveCertificate omega p d)
    (hcertDeriv : BranchSeedDerivativeFactorCertificate g p d j) :
    BranchSeedCorrectionSolvedForAllErrors g omega p d j :=
  branchSeedCorrectionSolvedForAllErrors_of_zmodCertificate hseed hcertSolve
    (branchSeedDerivativeNonzeroModP_of_factorCertificate hcertDeriv)

/-- Extract a solved correction for one quotient. -/
theorem finiteHenselCorrectionSolved_of_forAllErrors
    {omega q p d : Nat}
    (h : HenselCorrectionSolvedForAllErrors omega p d) :
    FiniteHenselCorrectionSolved omega q p d :=
  h q

end ApparitionDepth
