/-
  ABD.ApparitionDepth.HenselSimpleRootTheoremShape

  Step 21B of the Apparition-Depth Decomposition project.

  This file bundles the simple-root/Hensel theorem-shape from Steps 20A--20D into
  compact ready-to-use hypotheses.

  It does not prove Hensel's lemma.  Instead, it records the exact package of
  branch-seed data, derivative data, and finite-level Hensel exists-unique data
  needed to run the finite Teichmuller generation theorem without repeatedly
  passing many separate arguments.
-/

import ABD.ApparitionDepth.DerivativeNonzeroProof

namespace ApparitionDepth

/-! ## Ready packages for finite-level Hensel generation -/

/-- A branch seed is ready for the finite Teichmuller/Hensel generation theorem at
one fixed level.

This package contains exactly the hypotheses needed by the final theorem in
`TeichmullerFinite`, except the base-specific congruence witness
`BaseHasHenselLift`. -/
def BranchSeedHenselReadyAtLevel (g omega0 p d j r : Nat) : Prop :=
  PrimitiveRootModP g p ∧
    BranchParams p d j ∧
      BranchSeedModP g omega0 p d j ∧
        BranchSeedDerivativeNonzeroModP g p d j ∧
          HenselSimpleRootExistsUniqueAtLevel g p d j r

/-- The same fixed-level ready package, but using the explicit derivative factor
certificate from Step 21A instead of the already-compressed derivative condition. -/
def BranchSeedHenselReadyAtLevelFromFactors (g omega0 p d j r : Nat) : Prop :=
  PrimitiveRootModP g p ∧
    BranchParams p d j ∧
      BranchSeedModP g omega0 p d j ∧
        BranchSeedDerivativeFactorCertificate g p d j ∧
          HenselSimpleRootExistsUniqueAtLevel g p d j r

/-- A branch seed is ready at every positive finite level. -/
def BranchSeedHenselReadyForAllLevels (g omega0 p d j : Nat) : Prop :=
  PrimitiveRootModP g p ∧
    BranchParams p d j ∧
      BranchSeedModP g omega0 p d j ∧
        BranchSeedDerivativeNonzeroModP g p d j ∧
          HenselSimpleRootExistsUniqueForAllLevels g p d j

/-- The all-level ready package with the explicit derivative factor certificate. -/
def BranchSeedHenselReadyForAllLevelsFromFactors (g omega0 p d j : Nat) : Prop :=
  PrimitiveRootModP g p ∧
    BranchParams p d j ∧
      BranchSeedModP g omega0 p d j ∧
        BranchSeedDerivativeFactorCertificate g p d j ∧
          HenselSimpleRootExistsUniqueForAllLevels g p d j

/-! ## Constructors and projections -/

/-- Constructor for the fixed-level ready package. -/
theorem branchSeedHenselReadyAtLevel_intro {g omega0 p d j r : Nat}
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hhensel : HenselSimpleRootExistsUniqueAtLevel g p d j r) :
    BranchSeedHenselReadyAtLevel g omega0 p d j r :=
  ⟨hprim, hparams, hseed, hderiv, hhensel⟩

/-- Primitive-root data from the fixed-level ready package. -/
theorem branchSeedHenselReadyAtLevel_primitiveRoot {g omega0 p d j r : Nat}
    (h : BranchSeedHenselReadyAtLevel g omega0 p d j r) :
    PrimitiveRootModP g p :=
  h.1

/-- Branch parameters from the fixed-level ready package. -/
theorem branchSeedHenselReadyAtLevel_params {g omega0 p d j r : Nat}
    (h : BranchSeedHenselReadyAtLevel g omega0 p d j r) :
    BranchParams p d j :=
  h.2.1

/-- Seed equality from the fixed-level ready package. -/
theorem branchSeedHenselReadyAtLevel_seed {g omega0 p d j r : Nat}
    (h : BranchSeedHenselReadyAtLevel g omega0 p d j r) :
    BranchSeedModP g omega0 p d j :=
  h.2.2.1

/-- Derivative nonzero condition from the fixed-level ready package. -/
theorem branchSeedHenselReadyAtLevel_derivative {g omega0 p d j r : Nat}
    (h : BranchSeedHenselReadyAtLevel g omega0 p d j r) :
    BranchSeedDerivativeNonzeroModP g p d j :=
  h.2.2.2.1

/-- Hensel exists-unique theorem-shape from the fixed-level ready package. -/
theorem branchSeedHenselReadyAtLevel_hensel {g omega0 p d j r : Nat}
    (h : BranchSeedHenselReadyAtLevel g omega0 p d j r) :
    HenselSimpleRootExistsUniqueAtLevel g p d j r :=
  h.2.2.2.2

/-- Convert the factor-certificate version of the package into the compressed
fixed-level ready package. -/
theorem branchSeedHenselReadyAtLevel_of_factorCertificate {g omega0 p d j r : Nat}
    (h : BranchSeedHenselReadyAtLevelFromFactors g omega0 p d j r) :
    BranchSeedHenselReadyAtLevel g omega0 p d j r :=
  branchSeedHenselReadyAtLevel_intro
    h.1
    h.2.1
    h.2.2.1
    (branchSeedDerivativeNonzeroModP_of_factorCertificate h.2.2.2.1)
    h.2.2.2.2

/-- Extract a fixed-level ready package from the all-level ready package. -/
theorem branchSeedHenselReadyForAllLevels_at {g omega0 p d j r : Nat}
    (h : BranchSeedHenselReadyForAllLevels g omega0 p d j)
    (hr_pos : 0 < r) :
    BranchSeedHenselReadyAtLevel g omega0 p d j r :=
  branchSeedHenselReadyAtLevel_intro
    h.1
    h.2.1
    h.2.2.1
    h.2.2.2.1
    (henselSimpleRootExistsUniqueForAllLevels_at h.2.2.2.2 hr_pos)

/-- Extract a fixed-level ready package from the all-level factor-certificate
package. -/
theorem branchSeedHenselReadyForAllLevelsFromFactors_at {g omega0 p d j r : Nat}
    (h : BranchSeedHenselReadyForAllLevelsFromFactors g omega0 p d j)
    (hr_pos : 0 < r) :
    BranchSeedHenselReadyAtLevel g omega0 p d j r :=
  branchSeedHenselReadyAtLevel_intro
    h.1
    h.2.1
    h.2.2.1
    (branchSeedDerivativeNonzeroModP_of_factorCertificate h.2.2.2.1)
    (henselSimpleRootExistsUniqueForAllLevels_at h.2.2.2.2 hr_pos)

/-! ## Consequences of the ready package -/

/-- The ready package provides the level-one admissible Hensel input. -/
theorem henselAdmissibleLiftAtLevelOne_of_branchSeedHenselReadyAtLevel
    {g omega0 p d j r : Nat}
    (h : BranchSeedHenselReadyAtLevel g omega0 p d j r) :
    HenselAdmissibleLiftAtLevelOne g omega0 p d j :=
  henselAdmissibleLiftAtLevelOne_of_branchSeed_of_primitiveRoot_derivative
    (branchSeedHenselReadyAtLevel_primitiveRoot h)
    (branchSeedHenselReadyAtLevel_params h)
    (branchSeedHenselReadyAtLevel_seed h)
    (branchSeedHenselReadyAtLevel_derivative h)

/-- The ready package gives the existing fixed-level Hensel exists-unique
interface. -/
theorem henselLiftExistsUnique_of_branchSeedHenselReadyAtLevel
    {g omega0 p d j r : Nat}
    (h : BranchSeedHenselReadyAtLevel g omega0 p d j r) :
    HenselLiftExistsUnique g p d j r :=
  henselLiftExistsUnique_of_branchSeed_of_primitiveRoot_derivative
    (branchSeedHenselReadyAtLevel_hensel h)
    (branchSeedHenselReadyAtLevel_primitiveRoot h)
    (branchSeedHenselReadyAtLevel_params h)
    (branchSeedHenselReadyAtLevel_seed h)
    (branchSeedHenselReadyAtLevel_derivative h)

/-- The ready package produces a finite Teichmuller representative at the fixed
level. -/
theorem teichmullerFiniteExistsAtLevel_of_branchSeedHenselReadyAtLevel
    {g omega0 p d j r : Nat}
    (h : BranchSeedHenselReadyAtLevel g omega0 p d j r) :
    TeichmullerFiniteExistsAtLevel g p d j r :=
  exists_teichmullerFiniteAtLevel_of_branchSeed_primitiveRoot_derivative
    (branchSeedHenselReadyAtLevel_hensel h)
    (branchSeedHenselReadyAtLevel_primitiveRoot h)
    (branchSeedHenselReadyAtLevel_params h)
    (branchSeedHenselReadyAtLevel_seed h)
    (branchSeedHenselReadyAtLevel_derivative h)

/-- If a positive base has a Hensel-lift witness and the branch is ready at the
fixed level, then Core depth at least `r` follows. -/
theorem depthAtLeast_of_branchSeedHenselReadyAtLevel
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (hready : BranchSeedHenselReadyAtLevel g omega0 p d j r)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  finiteTeichmullerGeneration_depthAtLeast
    hbase
    (branchSeedHenselReadyAtLevel_hensel hready)
    (branchSeedHenselReadyAtLevel_primitiveRoot hready)
    (branchSeedHenselReadyAtLevel_params hready)
    (branchSeedHenselReadyAtLevel_seed hready)
    (branchSeedHenselReadyAtLevel_derivative hready)
    hell_pos

/-- Valuation lower-bound consequence of the fixed-level ready package. -/
theorem le_depthValue_of_branchSeedHenselReadyAtLevel
    {ell g omega0 p d j r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hbase : BaseHasHenselLift ell g p d j r)
    (hready : BranchSeedHenselReadyAtLevel g omega0 p d j r)
    (hell_pos : 0 < ell) :
    r ≤ depthValue ell p d :=
  finiteTeichmullerGeneration_le_depthValue
    hN
    hbase
    (branchSeedHenselReadyAtLevel_hensel hready)
    (branchSeedHenselReadyAtLevel_primitiveRoot hready)
    (branchSeedHenselReadyAtLevel_params hready)
    (branchSeedHenselReadyAtLevel_seed hready)
    (branchSeedHenselReadyAtLevel_derivative hready)
    hell_pos

/-- Order-side combined consequence of the fixed-level ready package. -/
theorem firstWithDepthAtLeast_of_branchSeedHenselReadyAtLevel
    {ell g omega0 p d j r : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hbase : BaseHasHenselLift ell g p d j r)
    (hready : BranchSeedHenselReadyAtLevel g omega0 p d j r)
    (hell_pos : 0 < ell) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  finiteTeichmullerGeneration_firstWithDepthAtLeast
    hord
    hd_pos
    hbase
    (branchSeedHenselReadyAtLevel_hensel hready)
    (branchSeedHenselReadyAtLevel_primitiveRoot hready)
    (branchSeedHenselReadyAtLevel_params hready)
    (branchSeedHenselReadyAtLevel_seed hready)
    (branchSeedHenselReadyAtLevel_derivative hready)
    hell_pos

end ApparitionDepth
