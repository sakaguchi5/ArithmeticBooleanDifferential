/-
  ABD.ApparitionDepth2.Hensel

  Public Hensel layer.

  This file deliberately hides the archived interface/actual/final split behind
  a small set of public names.  The current proved route is the finite actual
  route from the archive.

  The important public refactor in this layer is that Hensel generation now
  exits first through `RootAtLevel`.  `DepthAtLeast` is then obtained only by the
  standard `RootAtLevel <-> DepthAtLeast` bridge.
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

/-- A base with a Hensel-lift witness is already a root at level `r`.

This is the canonical Hensel-side public exit.  Notice that no positivity of the
base is needed here; positivity is only required later when returning to the
Core divisibility/depth language. -/
theorem rootAtLevel_of_baseHasHenselLift
    {ell g p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r) :
    RootAtLevel ell p d r := by
  rcases ApparitionDepth.baseInOmegaBranch_exists_of_baseHasHenselLift hbase with
    ⟨omega, hbranch⟩
  exact rootAtLevel_of_baseInOmegaBranch hbranch

/-- The finite-Hensel route, residue-ring form.

The extra hypotheses are kept in the signature to mirror the existing final
route and to make this theorem a drop-in public replacement for the old
`DepthAtLeast`-first interface.  Internally the root statement follows from the
Hensel-lift witness itself. -/
theorem rootAtLevel_of_finiteHenselInput
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (_hinput : FiniteHenselInput g p d j)
    (_hr_pos : 0 < r)
    (_hprim : PrimitiveRootModP g p)
    (_hparams : BranchParams p d j)
    (_hseed : BranchSeedModP g omega0 p d j)
    (_hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    RootAtLevel ell p d r :=
  rootAtLevel_of_baseHasHenselLift hbase

/-- Factor-certificate version of the residue-ring finite-Hensel route. -/
theorem rootAtLevel_of_finiteHenselInput_factorCertificate
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (_hinput : FiniteHenselInput g p d j)
    (_hr_pos : 0 < r)
    (_hprim : PrimitiveRootModP g p)
    (_hparams : BranchParams p d j)
    (_hseed : BranchSeedModP g omega0 p d j)
    (_hcert : BranchSeedDerivativeFactorCertificate g p d j) :
    RootAtLevel ell p d r :=
  rootAtLevel_of_baseHasHenselLift hbase

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
  depthAtLeast_of_rootAtLevel_of_base_pos hell_pos
    (rootAtLevel_of_finiteHenselInput
      hbase hinput hr_pos hprim hparams hseed hderiv)

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
  depthAtLeast_of_rootAtLevel_of_base_pos hell_pos
    (rootAtLevel_of_finiteHenselInput_factorCertificate
      hbase hinput hr_pos hprim hparams hseed hcert)

end ApparitionDepth2
