/-
  ABD.ApparitionDepth.FiniteHenselOneStepFinal

  Step 21E-Final of the Apparition-Depth Decomposition project.

  This file closes the local one-step route back into the finite-Hensel induction
  input from Step 21D.  Once base uniqueness, one-step existence proofs, and
  one-step uniqueness proofs are supplied, the whole AD/Hensel pipeline is
  available.
-/

import ABD.ApparitionDepth.StepUniquenessProof

namespace ApparitionDepth

/-! ## One-step proof input for the finite-Hensel route -/

/-- The local one-step proof input needed to build the finite-Hensel induction
input.

Compared with `FiniteHenselInductionInput`, this version keeps the one-step
existence and uniqueness in the more explicit proof-package form introduced in
Step 21E. -/
def FiniteHenselOneStepProofInput (g p d j : Nat) : Prop :=
  FiniteHenselBaseUniqueAtLevelOne g p d j ∧
    FiniteHenselOneStepExistenceProofForAllLevels g p d j ∧
      FiniteHenselOneStepUniquenessProofForAllLevels g p d j

/-- Constructor for the local one-step proof input. -/
theorem finiteHenselOneStepProofInput_intro {g p d j : Nat}
    (hbase : FiniteHenselBaseUniqueAtLevelOne g p d j)
    (hexists : FiniteHenselOneStepExistenceProofForAllLevels g p d j)
    (huniq : FiniteHenselOneStepUniquenessProofForAllLevels g p d j) :
    FiniteHenselOneStepProofInput g p d j :=
  ⟨hbase, hexists, huniq⟩

/-- Projection: base uniqueness at level one. -/
theorem finiteHenselOneStepProofInput_baseUnique {g p d j : Nat}
    (h : FiniteHenselOneStepProofInput g p d j) :
    FiniteHenselBaseUniqueAtLevelOne g p d j :=
  h.1

/-- Projection: one-step existence proof for all levels. -/
theorem finiteHenselOneStepProofInput_stepExists {g p d j : Nat}
    (h : FiniteHenselOneStepProofInput g p d j) :
    FiniteHenselOneStepExistenceProofForAllLevels g p d j :=
  h.2.1

/-- Projection: one-step uniqueness proof for all levels. -/
theorem finiteHenselOneStepProofInput_stepUnique {g p d j : Nat}
    (h : FiniteHenselOneStepProofInput g p d j) :
    FiniteHenselOneStepUniquenessProofForAllLevels g p d j :=
  h.2.2

/-- Convert the local one-step proof input into the induction input from Step 21D. -/
theorem finiteHenselInductionInput_of_oneStepProofInput {g p d j : Nat}
    (h : FiniteHenselOneStepProofInput g p d j) :
    FiniteHenselInductionInput g p d j :=
  finiteHenselInductionInput_intro
    (finiteHenselOneStepProofInput_baseUnique h)
    (finiteHenselStepExistenceForAllLevels_of_oneStepProofForAllLevels
      (finiteHenselOneStepProofInput_stepExists h))
    (finiteHenselStepUniqueForAllLevels_of_oneStepUniquenessProofForAllLevels
      (finiteHenselOneStepProofInput_stepUnique h))

/-- One-step proof input gives fixed-level Hensel exists-unique. -/
theorem henselSimpleRootExistsUniqueAtLevel_of_oneStepProofInput
    {g p d j r : Nat}
    (h : FiniteHenselOneStepProofInput g p d j)
    (hr_pos : 0 < r) :
    HenselSimpleRootExistsUniqueAtLevel g p d j r :=
  henselSimpleRootExistsUniqueAtLevel_of_finiteHenselInput
    (finiteHenselInductionInput_of_oneStepProofInput h)
    hr_pos

/-- One-step proof input gives all-level Hensel exists-unique. -/
theorem henselSimpleRootExistsUniqueForAllLevels_of_oneStepProofInput
    {g p d j : Nat}
    (h : FiniteHenselOneStepProofInput g p d j) :
    HenselSimpleRootExistsUniqueForAllLevels g p d j :=
  henselSimpleRootExistsUniqueForAllLevels_of_finiteHenselInput
    (finiteHenselInductionInput_of_oneStepProofInput h)

/-- One-step proof input gives a fixed-level branch-ready package. -/
theorem branchSeedHenselReadyAtLevel_of_oneStepProofInput
    {g omega0 p d j r : Nat}
    (h : FiniteHenselOneStepProofInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    BranchSeedHenselReadyAtLevel g omega0 p d j r :=
  branchSeedHenselReadyAtLevel_of_finiteHenselInput
    (finiteHenselInductionInput_of_oneStepProofInput h)
    hr_pos hprim hparams hseed hderiv

/-- Factor-certificate version of the fixed-level branch-ready package. -/
theorem branchSeedHenselReadyAtLevelFromFactors_of_oneStepProofInput
    {g omega0 p d j r : Nat}
    (h : FiniteHenselOneStepProofInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j) :
    BranchSeedHenselReadyAtLevel g omega0 p d j r :=
  branchSeedHenselReadyAtLevelFromFactors_of_finiteHenselInput
    (finiteHenselInductionInput_of_oneStepProofInput h)
    hr_pos hprim hparams hseed hcert

/-! ## Final AD consequences from one-step proof input -/

/-- Final one-step route to Core depth. -/
theorem finiteHenselOneStepFinal_depthAtLeast
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (h : FiniteHenselOneStepProofInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  finiteHenselFinal_depthAtLeast hbase
    (finiteHenselInductionInput_of_oneStepProofInput h)
    hr_pos hprim hparams hseed hderiv hell_pos

/-- Final one-step route to valuation lower bounds. -/
theorem finiteHenselOneStepFinal_le_depthValue
    {ell g omega0 p d j r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hbase : BaseHasHenselLift ell g p d j r)
    (h : FiniteHenselOneStepProofInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hell_pos : 0 < ell) :
    r ≤ depthValue ell p d :=
  finiteHenselFinal_le_depthValue hN hbase
    (finiteHenselInductionInput_of_oneStepProofInput h)
    hr_pos hprim hparams hseed hderiv hell_pos

/-- Final one-step route combined with the order side of apparition. -/
theorem finiteHenselOneStepFinal_firstWithDepthAtLeast
    {ell g omega0 p d j r : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hbase : BaseHasHenselLift ell g p d j r)
    (h : FiniteHenselOneStepProofInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hell_pos : 0 < ell) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  finiteHenselFinal_firstWithDepthAtLeast hord hd_pos hbase
    (finiteHenselInductionInput_of_oneStepProofInput h)
    hr_pos hprim hparams hseed hderiv hell_pos

/-- Factor-certificate version of the final Core-depth theorem. -/
theorem finiteHenselOneStepFinal_depthAtLeast_of_factorCertificate
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (h : FiniteHenselOneStepProofInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  finiteHenselFinal_depthAtLeast_of_factorCertificate hbase
    (finiteHenselInductionInput_of_oneStepProofInput h)
    hr_pos hprim hparams hseed hcert hell_pos

end ApparitionDepth
