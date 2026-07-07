/-
  ABD.ApparitionDepth.DerivativeNonzeroProof

  Step 21A of the Apparition-Depth Decomposition project.

  This file reduces the derivative-nonzero hypothesis used by the finite
  Teichmuller/Hensel generation pipeline to an explicit factor certificate.

  For the branch seed

      seed = g ^ (((p - 1) / d) * j)  in ZMod p,

  the derivative of X^d - 1 at the seed is

      d * seed^(d - 1).

  The genuinely algebraic finite-field proof that this product is nonzero from
  primality/unit hypotheses is intentionally left to a later, heavier layer.
  Here we isolate the exact certificate needed, and prove that once it is
  supplied, all previously-built simple-root and finite-Teichmuller generation
  theorems can be used without carrying an opaque derivative hypothesis.
-/

import ABD.ApparitionDepth.TeichmullerFinite

namespace ApparitionDepth

/-! ## Explicit factor certificate for the branch derivative -/

/-- An explicit certificate that the derivative

`d * seed^(d - 1)`

is nonzero in `ZMod p`, together with its two visible factors being nonzero.

The final conjunct is the actual derivative nonvanishing statement.  The first
and second conjuncts are kept as named data because the later finite-field proof
will naturally prove those factors first and then use that `ZMod p` is a field
when `p` is prime. -/
def BranchSeedDerivativeFactorCertificate (g p d j : Nat) : Prop :=
  (d : ZMod p) ≠ 0 ∧
    (branchSeedValue g p d j) ^ (d - 1) ≠ 0 ∧
      (d : ZMod p) * (branchSeedValue g p d j) ^ (d - 1) ≠ 0

/-- Constructor for the explicit derivative factor certificate. -/
theorem branchSeedDerivativeFactorCertificate_intro {g p d j : Nat}
    (hd_ne : (d : ZMod p) ≠ 0)
    (hpow_ne : (branchSeedValue g p d j) ^ (d - 1) ≠ 0)
    (hmul_ne : (d : ZMod p) * (branchSeedValue g p d j) ^ (d - 1) ≠ 0) :
    BranchSeedDerivativeFactorCertificate g p d j :=
  ⟨hd_ne, hpow_ne, hmul_ne⟩

/-- Projection: the coefficient `d` is nonzero in `ZMod p`. -/
theorem branchSeedDerivativeFactorCertificate_d_ne {g p d j : Nat}
    (h : BranchSeedDerivativeFactorCertificate g p d j) :
    (d : ZMod p) ≠ 0 :=
  h.1

/-- Projection: the seed-power factor is nonzero in `ZMod p`. -/
theorem branchSeedDerivativeFactorCertificate_pow_ne {g p d j : Nat}
    (h : BranchSeedDerivativeFactorCertificate g p d j) :
    (branchSeedValue g p d j) ^ (d - 1) ≠ 0 :=
  h.2.1

/-- Projection: the full derivative product is nonzero in `ZMod p`. -/
theorem branchSeedDerivativeFactorCertificate_mul_ne {g p d j : Nat}
    (h : BranchSeedDerivativeFactorCertificate g p d j) :
    (d : ZMod p) * (branchSeedValue g p d j) ^ (d - 1) ≠ 0 :=
  h.2.2

/-- The explicit factor certificate implies the existing branch-seed derivative
nonzero condition from Step 20A. -/
theorem branchSeedDerivativeNonzeroModP_of_factorCertificate {g p d j : Nat}
    (h : BranchSeedDerivativeFactorCertificate g p d j) :
    BranchSeedDerivativeNonzeroModP g p d j := by
  unfold BranchSeedDerivativeNonzeroModP branchSeedDerivativeValue
  exact branchSeedDerivativeFactorCertificate_mul_ne h

/-- Direct constructor for the existing derivative nonzero condition from the
full product inequality. -/
theorem branchSeedDerivativeNonzeroModP_of_mul_ne {g p d j : Nat}
    (h : (d : ZMod p) * (branchSeedValue g p d j) ^ (d - 1) ≠ 0) :
    BranchSeedDerivativeNonzeroModP g p d j := by
  unfold BranchSeedDerivativeNonzeroModP branchSeedDerivativeValue
  exact h

/-! ## Simple-root consequences of the derivative certificate -/

/-- Primitive-root branch data plus the explicit derivative factor certificate
makes the branch seed a simple root modulo `p`. -/
theorem branchSeedSimpleRootModP_of_primitiveRoot_factorCertificate
    {g p d j : Nat}
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j) :
    BranchSeedSimpleRootModP g p d j :=
  branchSeedSimpleRootModP_of_primitiveRoot_derivative hprim hparams
    (branchSeedDerivativeNonzeroModP_of_factorCertificate hcert)

/-- If `omega` represents the branch seed modulo `p`, then primitive-root branch
seed data plus the derivative factor certificate makes `omega` a simple root
modulo `p`. -/
theorem simpleRootModP_of_branchSeed_primitiveRoot_factorCertificate
    {g omega p d j : Nat}
    (hseed : BranchSeedModP g omega p d j)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j) :
    SimpleRootModP omega p d :=
  simpleRootModP_of_branchSeed_of_primitiveRoot_derivative hseed hprim hparams
    (branchSeedDerivativeNonzeroModP_of_factorCertificate hcert)

/-- Primitive-root branch seed data plus the derivative factor certificate gives
the level-one admissible Hensel input. -/
theorem henselAdmissibleLiftAtLevelOne_of_branchSeed_primitiveRoot_factorCertificate
    {g omega p d j : Nat}
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j) :
    HenselAdmissibleLiftAtLevelOne g omega p d j :=
  henselAdmissibleLiftAtLevelOne_of_branchSeed_of_primitiveRoot_derivative
    hprim hparams hseed
    (branchSeedDerivativeNonzeroModP_of_factorCertificate hcert)

/-! ## Finite Teichmuller generation using the explicit certificate -/

/-- The finite Teichmuller generation theorem for Core depth, with the derivative
hypothesis supplied by an explicit factor certificate. -/
theorem finiteTeichmullerGeneration_depthAtLeast_of_derivativeFactorCertificate
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (h : HenselSimpleRootExistsUniqueAtLevel g p d j r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  finiteTeichmullerGeneration_depthAtLeast hbase h hprim hparams hseed
    (branchSeedDerivativeNonzeroModP_of_factorCertificate hcert)
    hell_pos

/-- The finite Teichmuller generation theorem for valuation lower bounds, with
the derivative hypothesis supplied by an explicit factor certificate. -/
theorem finiteTeichmullerGeneration_le_depthValue_of_derivativeFactorCertificate
    {ell g omega0 p d j r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hbase : BaseHasHenselLift ell g p d j r)
    (h : HenselSimpleRootExistsUniqueAtLevel g p d j r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j)
    (hell_pos : 0 < ell) :
    r ≤ depthValue ell p d :=
  finiteTeichmullerGeneration_le_depthValue hN hbase h hprim hparams hseed
    (branchSeedDerivativeNonzeroModP_of_factorCertificate hcert)
    hell_pos

/-- The finite Teichmuller generation theorem combined with the order side, with
the derivative hypothesis supplied by an explicit factor certificate. -/
theorem finiteTeichmullerGeneration_firstWithDepthAtLeast_of_derivativeFactorCertificate
    {ell g omega0 p d j r : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hbase : BaseHasHenselLift ell g p d j r)
    (h : HenselSimpleRootExistsUniqueAtLevel g p d j r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j)
    (hell_pos : 0 < ell) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  finiteTeichmullerGeneration_firstWithDepthAtLeast hord hd_pos hbase h hprim hparams hseed
    (branchSeedDerivativeNonzeroModP_of_factorCertificate hcert)
    hell_pos

end ApparitionDepth
