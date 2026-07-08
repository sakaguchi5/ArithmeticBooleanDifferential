/-
  ABD.ApparitionDepth2.GeneratedRoot

  Public generated-root layer.

  This is the intended external surface of the current Teichmuller/Hensel side:
  a base in a generated branch inherits depth, and with order control it inherits
  first-apparition-with-depth.
-/

import ABD.ApparitionDepth.TeichmullerFinite
import ABD.ApparitionDepth2.Hensel
import ABD.ApparitionDepth2.Order

namespace ApparitionDepth2

/-- A base is generated at level `r` by the branch `(g,p,d,j)`. -/
abbrev GeneratedRoot (ell g p d j r : Nat) : Prop :=
  BaseHasHenselLift ell g p d j r

/-- A base lies in the finite Teichmuller branch at level `r`. -/
abbrev BaseInTeichmullerFiniteBranch (ell omega g p d j r : Nat) : Prop :=
  ApparitionDepth.BaseInTeichmullerFiniteBranch ell omega g p d j r

/-- Existential finite-Teichmuller branch membership. -/
abbrev BaseInSomeTeichmullerFiniteBranch (ell g p d j r : Nat) : Prop :=
  ApparitionDepth.BaseInSomeTeichmullerFiniteBranch ell g p d j r

/-- A positive base in a finite Teichmuller branch has core depth at least `r`. -/
theorem depthAtLeast_of_baseInTeichmullerFiniteBranch
    {ell omega g p d j r : Nat}
    (hbranch : BaseInTeichmullerFiniteBranch ell omega g p d j r)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  ApparitionDepth.depthAtLeast_of_baseInTeichmullerFiniteBranch_of_base_pos
    hbranch hell_pos

/-- Existential branch-membership form of generated depth. -/
theorem depthAtLeast_of_baseInSomeTeichmullerFiniteBranch
    {ell g p d j r : Nat}
    (hbranch : BaseInSomeTeichmullerFiniteBranch ell g p d j r)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  ApparitionDepth.depthAtLeast_of_baseInSomeTeichmullerFiniteBranch_of_base_pos
    hbranch hell_pos

/-- Fully packaged generated-depth theorem for the current finite-Hensel route. -/
theorem generated_depthAtLeast
    {ell g omega0 p d j r : Nat}
    (hgen : GeneratedRoot ell g p d j r)
    (hinput : FiniteHenselInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  depthAtLeast_of_finiteHenselInput
    hgen hinput hr_pos hprim hparams hseed hderiv hell_pos

/-- Factor-certificate version of generated depth. -/
theorem generated_depthAtLeast_factorCertificate
    {ell g omega0 p d j r : Nat}
    (hgen : GeneratedRoot ell g p d j r)
    (hinput : FiniteHenselInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  depthAtLeast_of_finiteHenselInput_factorCertificate
    hgen hinput hr_pos hprim hparams hseed hcert hell_pos

/-- Generated branch plus order control gives first apparition with depth at least `r`. -/
theorem generated_firstAppearsWithDepthAtLeast
    {ell g omega0 p d j r : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hgen : GeneratedRoot ell g p d j r)
    (hinput : FiniteHenselInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hell_pos : 0 < ell) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  ApparitionDepth.finiteHenselActualFinal_firstWithDepthAtLeast
    hord hd_pos hgen hinput hr_pos hprim hparams hseed hderiv hell_pos

/-- Factor-certificate form of the final generated theorem. -/
theorem generated_firstAppearsWithDepthAtLeast_factorCertificate
    {ell g omega0 p d j r : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hgen : GeneratedRoot ell g p d j r)
    (hinput : FiniteHenselInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j)
    (hell_pos : 0 < ell) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  generated_firstAppearsWithDepthAtLeast
    hord hd_pos hgen hinput hr_pos hprim hparams hseed
    (derivativeNonzero_of_factorCertificate hcert) hell_pos

end ApparitionDepth2
