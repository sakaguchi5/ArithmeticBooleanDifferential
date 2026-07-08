/-
  ABD.ApparitionDepth.FiniteHenselActualFinal

  Step 21M of the Apparition-Depth Decomposition project.

  This file packages the actual-route inputs from Steps 21F--21L and feeds them
  back into the already-built finite-Hensel / finite-Teichmuller / AD-depth
  pipeline.

  Status note:
  * base-level uniqueness is proved in Step 21F;
  * one-step existence and uniqueness are now represented by `Actual` packages;
  * once those actual packages are supplied, no Hensel theorem-shape is needed
    anymore at this final interface.
-/

import ABD.ApparitionDepth.OneStepUniquenessActual

namespace ApparitionDepth

/-! ## Final actual finite-Hensel input -/

/-- Actual finite-Hensel input: base uniqueness is automatic, while the remaining
local one-step existence and uniqueness data are supplied in the `Actual` form. -/
def FiniteHenselActualInput (g p d j : Nat) : Prop :=
  FiniteHenselOneStepExistenceActualForAllLevels g p d j ∧
    FiniteHenselOneStepUniquenessActualForAllLevels g p d j

/-- Constructor for the actual finite-Hensel input. -/
theorem finiteHenselActualInput_intro {g p d j : Nat}
    (hexists : FiniteHenselOneStepExistenceActualForAllLevels g p d j)
    (huniq : FiniteHenselOneStepUniquenessActualForAllLevels g p d j) :
    FiniteHenselActualInput g p d j :=
  ⟨hexists, huniq⟩

/-- Projection: actual one-step existence for all levels. -/
theorem finiteHenselActualInput_stepExists {g p d j : Nat}
    (h : FiniteHenselActualInput g p d j) :
    FiniteHenselOneStepExistenceActualForAllLevels g p d j :=
  h.1

/-- Projection: actual one-step uniqueness for all levels. -/
theorem finiteHenselActualInput_stepUnique {g p d j : Nat}
    (h : FiniteHenselActualInput g p d j) :
    FiniteHenselOneStepUniquenessActualForAllLevels g p d j :=
  h.2

/-- Convert the actual finite-Hensel input into the Step-21E one-step proof input.

The base-level uniqueness component is supplied by Step 21F. -/
theorem finiteHenselOneStepProofInput_of_actualInput {g p d j : Nat}
    (h : FiniteHenselActualInput g p d j) :
    FiniteHenselOneStepProofInput g p d j :=
  finiteHenselOneStepProofInput_of_oneStepProofs
    (finiteHenselOneStepExistenceProofForAllLevels_of_actualForAllLevels
      (finiteHenselActualInput_stepExists h))
    (finiteHenselOneStepUniquenessProofForAllLevels_of_actualForAllLevels
      (finiteHenselActualInput_stepUnique h))

/-- Convert the actual finite-Hensel input into the Step-21D induction input. -/
theorem finiteHenselInductionInput_of_actualInput {g p d j : Nat}
    (h : FiniteHenselActualInput g p d j) :
    FiniteHenselInductionInput g p d j :=
  finiteHenselInductionInput_of_oneStepProofInput
    (finiteHenselOneStepProofInput_of_actualInput h)

/-- Actual finite-Hensel input gives fixed-level Hensel exists-unique. -/
theorem henselSimpleRootExistsUniqueAtLevel_of_actualInput
    {g p d j r : Nat}
    (h : FiniteHenselActualInput g p d j)
    (hr_pos : 0 < r) :
    HenselSimpleRootExistsUniqueAtLevel g p d j r :=
  henselSimpleRootExistsUniqueAtLevel_of_oneStepProofInput
    (finiteHenselOneStepProofInput_of_actualInput h)
    hr_pos

/-- Actual finite-Hensel input gives all-level Hensel exists-unique. -/
theorem henselSimpleRootExistsUniqueForAllLevels_of_actualInput
    {g p d j : Nat}
    (h : FiniteHenselActualInput g p d j) :
    HenselSimpleRootExistsUniqueForAllLevels g p d j :=
  henselSimpleRootExistsUniqueForAllLevels_of_oneStepProofInput
    (finiteHenselOneStepProofInput_of_actualInput h)

/-- Actual finite-Hensel input gives a fixed-level branch-ready package. -/
theorem branchSeedHenselReadyAtLevel_of_actualInput
    {g omega0 p d j r : Nat}
    (hactual : FiniteHenselActualInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    BranchSeedHenselReadyAtLevel g omega0 p d j r :=
  branchSeedHenselReadyAtLevel_of_oneStepProofInput
    (finiteHenselOneStepProofInput_of_actualInput hactual)
    hr_pos hprim hparams hseed hderiv

/-- Factor-certificate version of branch readiness from actual finite-Hensel input. -/
theorem branchSeedHenselReadyAtLevelFromFactors_of_actualInput
    {g omega0 p d j r : Nat}
    (hactual : FiniteHenselActualInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j) :
    BranchSeedHenselReadyAtLevel g omega0 p d j r :=
  branchSeedHenselReadyAtLevelFromFactors_of_oneStepProofInput
    (finiteHenselOneStepProofInput_of_actualInput hactual)
    hr_pos hprim hparams hseed hcert

/-! ## Final AD consequences -/

/-- Final actual finite-Hensel route to Core depth. -/
theorem finiteHenselActualFinal_depthAtLeast
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (hactual : FiniteHenselActualInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  finiteHenselOneStepFinal_depthAtLeast hbase
    (finiteHenselOneStepProofInput_of_actualInput hactual)
    hr_pos hprim hparams hseed hderiv hell_pos

/-- Final actual finite-Hensel route to valuation lower bounds. -/
theorem finiteHenselActualFinal_le_depthValue
    {ell g omega0 p d j r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hbase : BaseHasHenselLift ell g p d j r)
    (hactual : FiniteHenselActualInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hell_pos : 0 < ell) :
    r ≤ depthValue ell p d :=
  finiteHenselOneStepFinal_le_depthValue hN hbase
    (finiteHenselOneStepProofInput_of_actualInput hactual)
    hr_pos hprim hparams hseed hderiv hell_pos

/-- Final actual finite-Hensel route combined with the order side of apparition. -/
theorem finiteHenselActualFinal_firstWithDepthAtLeast
    {ell g omega0 p d j r : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hbase : BaseHasHenselLift ell g p d j r)
    (hactual : FiniteHenselActualInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hell_pos : 0 < ell) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  finiteHenselOneStepFinal_firstWithDepthAtLeast hord hd_pos hbase
    (finiteHenselOneStepProofInput_of_actualInput hactual)
    hr_pos hprim hparams hseed hderiv hell_pos

/-- Factor-certificate version of the final actual Core-depth theorem. -/
theorem finiteHenselActualFinal_depthAtLeast_of_factorCertificate
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (hactual : FiniteHenselActualInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  finiteHenselOneStepFinal_depthAtLeast_of_factorCertificate hbase
    (finiteHenselOneStepProofInput_of_actualInput hactual)
    hr_pos hprim hparams hseed hcert hell_pos

end ApparitionDepth
