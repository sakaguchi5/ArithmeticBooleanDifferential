/-
  ABD.ApparitionDepth2.SimpleRoot

  Public simple-root layer.

  Public theorem theme:
    branch seed is a simple root of X^d - 1 modulo p.
-/

import ABD.ApparitionDepth.DerivativeNonzeroProof
import ABD.ApparitionDepth2.Branch

namespace ApparitionDepth2

/-- Derivative nonzero condition for the branch seed. -/
abbrev BranchSeedDerivativeNonzeroModP (g p d j : Nat) : Prop :=
  ApparitionDepth.BranchSeedDerivativeNonzeroModP g p d j

/-- Explicit factor certificate for the derivative of `X^d - 1` at the seed. -/
abbrev BranchSeedDerivativeFactorCertificate (g p d j : Nat) : Prop :=
  ApparitionDepth.BranchSeedDerivativeFactorCertificate g p d j

/-- Concrete simple-root package modulo `p`. -/
abbrev SimpleRootModP (omega p d : Nat) : Prop :=
  ApparitionDepth.SimpleRootModP omega p d

/-- Branch-seed simple-root package. -/
abbrev BranchSeedSimpleRootModP (g p d j : Nat) : Prop :=
  ApparitionDepth.BranchSeedSimpleRootModP g p d j

/-- Primitive-root branch data plus an explicit derivative certificate makes the branch seed simple. -/
theorem branch_seed_simpleRoot_of_factorCertificate
    {g p d j : Nat}
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j) :
    BranchSeedSimpleRootModP g p d j :=
  ApparitionDepth.branchSeedSimpleRootModP_of_primitiveRoot_factorCertificate
    hprim hparams hcert

/-- Concrete representative form of branch-seed simplicity. -/
theorem simpleRoot_of_branchSeed_factorCertificate
    {g omega p d j : Nat}
    (hseed : BranchSeedModP g omega p d j)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j) :
    SimpleRootModP omega p d :=
  ApparitionDepth.simpleRootModP_of_branchSeed_primitiveRoot_factorCertificate
    hseed hprim hparams hcert

/-- A factor certificate supplies the archived derivative-nonzero condition. -/
theorem derivativeNonzero_of_factorCertificate
    {g p d j : Nat}
    (hcert : BranchSeedDerivativeFactorCertificate g p d j) :
    BranchSeedDerivativeNonzeroModP g p d j :=
  ApparitionDepth.branchSeedDerivativeNonzeroModP_of_factorCertificate hcert

end ApparitionDepth2
