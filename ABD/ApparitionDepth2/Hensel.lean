/-
  ABD.ApparitionDepth2.Hensel

  Public Hensel layer.

  This file deliberately hides the archived interface/actual/final split behind
  a small set of public names.  The current proved route is the finite actual
  route from the archive.
-/

import ABD.ApparitionDepth.FiniteHenselActualFinal
import ABD.ApparitionDepth2.SimpleRoot

namespace ApparitionDepth2

/-- Current finite-Hensel actual input package from the archived proof. -/
abbrev FiniteHenselInput (g p d j : Nat) : Prop :=
  ApparitionDepth.FiniteHenselActualInput g p d j

/-- Archived simple-root exists-unique theorem shape at level `r`. -/
abbrev HenselSimpleRootExistsUniqueAtLevel (g p d j r : Nat) : Prop :=
  ApparitionDepth.HenselSimpleRootExistsUniqueAtLevel g p d j r

/-- A base is congruent to a Hensel lift of the branch seed. -/
abbrev BaseHasHenselLift (ell g p d j r : Nat) : Prop :=
  ApparitionDepth.BaseHasHenselLift ell g p d j r

/-- The actual finite-Hensel input gives the simple-root exists-unique theorem shape. -/
theorem simpleRoot_existsUniqueAtLevel_of_finiteHenselInput
    {g p d j r : Nat}
    (hinput : FiniteHenselInput g p d j)
    (hr_pos : 0 < r) :
    HenselSimpleRootExistsUniqueAtLevel g p d j r :=
  ApparitionDepth.henselSimpleRootExistsUniqueAtLevel_of_actualInput hinput hr_pos

/-- The finite-Hensel route turns branch membership into core depth. -/
theorem depthAtLeast_of_finiteHenselInput
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (hinput : FiniteHenselInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  ApparitionDepth.finiteHenselActualFinal_depthAtLeast
    hbase hinput hr_pos hprim hparams hseed hderiv hell_pos

/-- Factor-certificate version of the depth theorem. -/
theorem depthAtLeast_of_finiteHenselInput_factorCertificate
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (hinput : FiniteHenselInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  ApparitionDepth.finiteHenselActualFinal_depthAtLeast_of_factorCertificate
    hbase hinput hr_pos hprim hparams hseed hcert hell_pos

end ApparitionDepth2
