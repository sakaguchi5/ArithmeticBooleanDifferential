/-
  ABD.ApparitionDepth2.Main

  Public entrance for the new ApparitionDepth2 folder.

  This file intentionally exposes only the mathematical spine.  The old
  `ABD.ApparitionDepth` folder remains the archive of the detailed proof path.

  Current proved public spine:
    1. first apparition is controlled by multiplicative order;
    2. depth is controlled by root-at-level modulo p^r;
    3. branch seeds are roots, and with derivative certificate are simple roots;
    4. the finite Hensel actual route produces a generated RootAtLevel statement;
    5. RootAtLevel returns to DepthAtLeast only through the standard bridge;
    6. generated depth plus order gives first apparition with depth.

  Reserved future public spines, not implemented here yet:
    * cyclotomic exact-factor bridge;
    * primitive prime divisor bridge;
    * Witt/carry next-level bridge;
    * final synthesis theorem.
-/

import ABD.ApparitionDepth2.GeneratedRoot

namespace ApparitionDepth2

/-- Main current root-at-level theorem, derivative-nonzero version.

This is the preferred interface for the next folders.  Cyclotomic and Witt/carry
work should consume this residue-ring statement before asking for Core depth. -/
theorem main_generated_rootAtLevel
    {ell g omega0 p d j r : Nat}
    (hgen : GeneratedRoot ell g p d j r)
    (hinput : FiniteHenselInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    RootAtLevel ell p d r :=
  generated_rootAtLevel_of_finiteHenselInput
    hgen hinput hr_pos hprim hparams hseed hderiv

/-- Main current root-at-level theorem, explicit derivative-factor-certificate version. -/
theorem main_generated_rootAtLevel_factorCertificate
    {ell g omega0 p d j r : Nat}
    (hgen : GeneratedRoot ell g p d j r)
    (hinput : FiniteHenselInput g p d j)
    (hr_pos : 0 < r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hcert : BranchSeedDerivativeFactorCertificate g p d j) :
    RootAtLevel ell p d r :=
  generated_rootAtLevel_factorCertificate
    hgen hinput hr_pos hprim hparams hseed hcert

/-- Main current theorem, derivative-nonzero version. -/
theorem main_generated_firstAppearsWithDepthAtLeast
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
  generated_firstAppearsWithDepthAtLeast
    hord hd_pos hgen hinput hr_pos hprim hparams hseed hderiv hell_pos

/-- Main current theorem, explicit derivative-factor-certificate version. -/
theorem main_generated_firstAppearsWithDepthAtLeast_factorCertificate
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
  generated_firstAppearsWithDepthAtLeast_factorCertificate
    hord hd_pos hgen hinput hr_pos hprim hparams hseed hcert hell_pos

/-!
## Future public theorem names to add later

The following are intentionally documentation comments, not Lean declarations.
They are the planned public exits for the next folders.

* Cyclotomic side:
  - order implies `p | Phi_d(ell)`.
  - `RootAtLevel ell p d r` plus exact order implies `p^r | Phi_d(ell)` under
    the right no-contamination condition.

* Primitive prime divisor side:
  - primitive divisor of `ell^n - 1` implies first apparition at `n`.
  - nonprimitive factors split into earlier apparition indices.

* Witt/carry side:
  - carry condition at level `r` upgrades `RootAtLevel ell p d r` to
    `RootAtLevel ell p d (r+1)`.
  - Hensel correction digit agrees with the Witt/carry next-coordinate rule.

* Synthesis:
  - Teichmuller/Hensel generation + cyclotomic exact order + primitive divisor
    control + Witt/carry next-level rule closes the combined AD theorem.
-/

end ApparitionDepth2
