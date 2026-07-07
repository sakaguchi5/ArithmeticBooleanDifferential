/-
  ABD.ApparitionDepth.FiniteHenselFinal

  Step 21D-Final of the Apparition-Depth Decomposition project.

  This file closes the finite-Hensel route back into the existing AD interfaces.
  Once the finite step-existence/step-uniqueness induction input is supplied, it
  produces the same certificates that the mathlib-facing Hensel bridge expects,
  and therefore feeds the finite Teichmuller generation pipeline.
-/

import ABD.ApparitionDepth.FiniteHenselInduction

namespace ApparitionDepth

/-! ## Finite-Hensel induction as a Hensel certificate -/

/-- A finite-Hensel induction certificate is exactly the fixed-level certificate
expected by the mathlib-facing bridge. -/
theorem henselMathlibCertificateAtLevel_of_finiteHenselInductionCertificate
    {g p d j r : Nat}
    (hcert : FiniteHenselInductionCertificateAtLevel g p d j r) :
    HenselMathlibCertificateAtLevel g p d j r :=
  hcert

/-- All-level finite-Hensel induction certificates give the all-level mathlib-facing
certificate. -/
theorem henselMathlibCertificateForAllLevels_of_finiteHenselInductionCertificate
    {g p d j : Nat}
    (hcert : FiniteHenselInductionCertificateForAllLevels g p d j) :
    HenselMathlibCertificateForAllLevels g p d j :=
  hcert

/-- Fixed-level Hensel exists-unique theorem-shape from a finite-Hensel induction
certificate. -/
theorem henselSimpleRootExistsUniqueAtLevel_of_finiteHenselInductionCertificate
    {g p d j r : Nat}
    (hcert : FiniteHenselInductionCertificateAtLevel g p d j r) :
    HenselSimpleRootExistsUniqueAtLevel g p d j r :=
  henselSimpleRootExistsUniqueAtLevel_of_mathlibCertificate
    (henselMathlibCertificateAtLevel_of_finiteHenselInductionCertificate hcert)

/-- All-level Hensel exists-unique theorem-shape from finite-Hensel induction
certificates. -/
theorem henselSimpleRootExistsUniqueForAllLevels_of_finiteHenselInductionCertificate
    {g p d j : Nat}
    (hcert : FiniteHenselInductionCertificateForAllLevels g p d j) :
    HenselSimpleRootExistsUniqueForAllLevels g p d j :=
  henselSimpleRootExistsUniqueForAllLevels_of_mathlibCertificate
    (henselMathlibCertificateForAllLevels_of_finiteHenselInductionCertificate hcert)

/-- Fixed-level Hensel exists-unique theorem-shape directly from finite-Hensel
induction input. -/
theorem henselSimpleRootExistsUniqueAtLevel_of_finiteHenselInput
    {g p d j r : Nat}
    (hinput : FiniteHenselInductionInput g p d j)
    (hr_pos : 0 < r) :
    HenselSimpleRootExistsUniqueAtLevel g p d j r :=
  henselSimpleRootExistsUniqueAtLevel_of_finiteHenselInductionCertificate
    (finiteHenselInductionCertificateAtLevel_of_input hinput hr_pos)

/-- All-level Hensel exists-unique theorem-shape directly from finite-Hensel
induction input. -/
theorem henselSimpleRootExistsUniqueForAllLevels_of_finiteHenselInput
    {g p d j : Nat}
    (hinput : FiniteHenselInductionInput g p d j) :
    HenselSimpleRootExistsUniqueForAllLevels g p d j :=
  henselSimpleRootExistsUniqueForAllLevels_of_finiteHenselInductionCertificate
    (finiteHenselInductionCertificateForAllLevels_of_input hinput)

/-! ## Ready packages from finite-Hensel induction -/

/-- Finite-Hensel induction input gives a mathlib-ready package at a fixed level. -/
theorem branchSeedMathlibReadyAtLevel_of_finiteHenselInput
    {g omega0 p d j r : Nat}
    (hinput : FiniteHenselInductionInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    BranchSeedMathlibReadyAtLevel g omega0 p d j r :=
  branchSeedMathlibReadyAtLevel_intro
    hprim hparams hseed hderiv
    (henselMathlibCertificateAtLevel_of_finiteHenselInductionCertificate
      (finiteHenselInductionCertificateAtLevel_of_input hinput hr_pos))

/-- Factor-certificate version of the previous theorem. -/
theorem branchSeedMathlibReadyAtLevelFromFactors_of_finiteHenselInput
    {g omega0 p d j r : Nat}
    (hinput : FiniteHenselInductionInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j) :
    BranchSeedMathlibReadyAtLevelFromFactors g omega0 p d j r :=
  ⟨hprim, hparams, hseed, hcert,
    henselMathlibCertificateAtLevel_of_finiteHenselInductionCertificate
      (finiteHenselInductionCertificateAtLevel_of_input hinput hr_pos)⟩

/-- Finite-Hensel induction input gives the compact branch-ready package from
Step 21B. -/
theorem branchSeedHenselReadyAtLevel_of_finiteHenselInput
    {g omega0 p d j r : Nat}
    (hinput : FiniteHenselInductionInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    BranchSeedHenselReadyAtLevel g omega0 p d j r :=
  branchSeedHenselReadyAtLevel_of_mathlibReadyAtLevel
    (branchSeedMathlibReadyAtLevel_of_finiteHenselInput
      hinput hr_pos hprim hparams hseed hderiv)

/-- Factor-certificate version of the compact branch-ready package. -/
theorem branchSeedHenselReadyAtLevelFromFactors_of_finiteHenselInput
    {g omega0 p d j r : Nat}
    (hinput : FiniteHenselInductionInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j) :
    BranchSeedHenselReadyAtLevel g omega0 p d j r :=
  branchSeedHenselReadyAtLevel_of_mathlibReadyAtLevelFromFactors
    (branchSeedMathlibReadyAtLevelFromFactors_of_finiteHenselInput
      hinput hr_pos hprim hparams hseed hcert)

/-- All-level mathlib-ready package from finite-Hensel induction input. -/
theorem branchSeedMathlibReadyForAllLevels_of_finiteHenselInput
    {g omega0 p d j : Nat}
    (hinput : FiniteHenselInductionInput g p d j)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    BranchSeedMathlibReadyForAllLevels g omega0 p d j :=
  ⟨hprim, hparams, hseed, hderiv,
    henselMathlibCertificateForAllLevels_of_finiteHenselInductionCertificate
      (finiteHenselInductionCertificateForAllLevels_of_input hinput)⟩

/-- All-level factor-certificate mathlib-ready package from finite-Hensel induction
input. -/
theorem branchSeedMathlibReadyForAllLevelsFromFactors_of_finiteHenselInput
    {g omega0 p d j : Nat}
    (hinput : FiniteHenselInductionInput g p d j)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j) :
    BranchSeedMathlibReadyForAllLevelsFromFactors g omega0 p d j :=
  ⟨hprim, hparams, hseed, hcert,
    henselMathlibCertificateForAllLevels_of_finiteHenselInductionCertificate
      (finiteHenselInductionCertificateForAllLevels_of_input hinput)⟩

/-! ## Final consequences for AD depth -/

/-- Final finite-Hensel route to Core depth. -/
theorem finiteHenselFinal_depthAtLeast
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (hinput : FiniteHenselInductionInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  depthAtLeast_of_branchSeedHenselReadyAtLevel hbase
    (branchSeedHenselReadyAtLevel_of_finiteHenselInput
      hinput hr_pos hprim hparams hseed hderiv)
    hell_pos

/-- Final finite-Hensel route to valuation lower bounds. -/
theorem finiteHenselFinal_le_depthValue
    {ell g omega0 p d j r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hbase : BaseHasHenselLift ell g p d j r)
    (hinput : FiniteHenselInductionInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hell_pos : 0 < ell) :
    r ≤ depthValue ell p d :=
  le_depthValue_of_branchSeedHenselReadyAtLevel hN hbase
    (branchSeedHenselReadyAtLevel_of_finiteHenselInput
      hinput hr_pos hprim hparams hseed hderiv)
    hell_pos

/-- Final finite-Hensel route combined with the order side of apparition. -/
theorem finiteHenselFinal_firstWithDepthAtLeast
    {ell g omega0 p d j r : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hbase : BaseHasHenselLift ell g p d j r)
    (hinput : FiniteHenselInductionInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hell_pos : 0 < ell) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  firstWithDepthAtLeast_of_branchSeedHenselReadyAtLevel
    hord hd_pos hbase
    (branchSeedHenselReadyAtLevel_of_finiteHenselInput
      hinput hr_pos hprim hparams hseed hderiv)
    hell_pos

/-- Factor-certificate version of the final Core-depth theorem. -/
theorem finiteHenselFinal_depthAtLeast_of_factorCertificate
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (hinput : FiniteHenselInductionInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  depthAtLeast_of_branchSeedHenselReadyAtLevel hbase
    (branchSeedHenselReadyAtLevelFromFactors_of_finiteHenselInput
      hinput hr_pos hprim hparams hseed hcert)
    hell_pos

end ApparitionDepth
