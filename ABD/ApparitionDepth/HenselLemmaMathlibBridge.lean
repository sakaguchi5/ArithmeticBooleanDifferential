/-
  ABD.ApparitionDepth.HenselLemmaMathlibBridge

  Step 21C of the Apparition-Depth Decomposition project.

  This file is the bridge point between a future mathlib-facing Hensel lemma and
  the finite Apparition-Depth interfaces already built.

  Important status note:
    this file still does not prove Hensel's lemma.  Instead, it names the exact
    certificate that a mathlib Hensel theorem should provide, and proves that
    such a certificate immediately gives the existing AD theorem-shapes:

      HenselSimpleRootExistsUniqueAtLevel
      BranchSeedHenselReadyAtLevel
      TeichmullerFiniteExistsAtLevel
      DepthAtLeast
      r <= depthValue
      FirstAppearsWithDepthAtLeast

  Thus later work can focus only on producing the mathlib certificate; all
  transport back into the AD pipeline is already handled here.
-/

import ABD.ApparitionDepth.HenselSimpleRootTheoremShape

namespace ApparitionDepth

/-! ## Mathlib-facing Hensel certificates -/

/-- Fixed-level certificate expected from a future mathlib Hensel lemma.

For the branch `(g,p,d,j)` and level `r`, it says that every admissible level-one
simple root produces existence and uniqueness of the finite Hensel lift at level
`p^r`.

This is intentionally phrased in the already-built AD language, so that a later
file only has to translate a genuine mathlib Hensel statement into this
certificate. -/
def HenselMathlibCertificateAtLevel (g p d j r : Nat) : Prop :=
  ∀ omega0 : Nat,
    HenselAdmissibleLiftAtLevelOne g omega0 p d j →
      HenselLiftExistsUnique g p d j r

/-- All-level version of the mathlib-facing Hensel certificate. -/
def HenselMathlibCertificateForAllLevels (g p d j : Nat) : Prop :=
  ∀ r : Nat, 0 < r → HenselMathlibCertificateAtLevel g p d j r

/-- Constructor for the fixed-level mathlib-facing certificate. -/
theorem henselMathlibCertificateAtLevel_intro {g p d j r : Nat}
    (h : ∀ omega0 : Nat,
      HenselAdmissibleLiftAtLevelOne g omega0 p d j →
        HenselLiftExistsUnique g p d j r) :
    HenselMathlibCertificateAtLevel g p d j r :=
  h

/-- Apply a fixed-level mathlib-facing certificate to a level-one admissible lift. -/
theorem henselMathlibCertificateAtLevel_apply
    {g omega0 p d j r : Nat}
    (hmath : HenselMathlibCertificateAtLevel g p d j r)
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j) :
    HenselLiftExistsUnique g p d j r :=
  hmath omega0 hadm

/-- Extract a fixed-level certificate from the all-level certificate. -/
theorem henselMathlibCertificateForAllLevels_at {g p d j r : Nat}
    (hmath : HenselMathlibCertificateForAllLevels g p d j)
    (hr_pos : 0 < r) :
    HenselMathlibCertificateAtLevel g p d j r :=
  hmath r hr_pos

/-! ## Conversion to the existing simple-root theorem-shapes -/

/-- A mathlib-facing fixed-level certificate gives the existing fixed-level
simple-root exists-unique theorem-shape. -/
theorem henselSimpleRootExistsUniqueAtLevel_of_mathlibCertificate
    {g p d j r : Nat}
    (hmath : HenselMathlibCertificateAtLevel g p d j r) :
    HenselSimpleRootExistsUniqueAtLevel g p d j r := by
  refine ⟨?_, ?_⟩
  · intro omega0 hadm
    exact henselLiftExistsUnique_exists
      (henselMathlibCertificateAtLevel_apply hmath hadm)
  · intro omega0 hadm
    exact henselLiftExistsUnique_unique
      (henselMathlibCertificateAtLevel_apply hmath hadm)

/-- All-level mathlib-facing certificates give the existing all-level
simple-root exists-unique theorem-shape. -/
theorem henselSimpleRootExistsUniqueForAllLevels_of_mathlibCertificate
    {g p d j : Nat}
    (hmath : HenselMathlibCertificateForAllLevels g p d j) :
    HenselSimpleRootExistsUniqueForAllLevels g p d j :=
  fun _r hr_pos =>
    henselSimpleRootExistsUniqueAtLevel_of_mathlibCertificate
      (henselMathlibCertificateForAllLevels_at hmath hr_pos)

/-- A fixed-level mathlib-facing certificate gives the existing fixed-level
Hensel exists-unique interface once a level-one admissible lift is supplied. -/
theorem henselLiftExistsUnique_of_mathlibCertificate
    {g omega0 p d j r : Nat}
    (hmath : HenselMathlibCertificateAtLevel g p d j r)
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j) :
    HenselLiftExistsUnique g p d j r :=
  henselMathlibCertificateAtLevel_apply hmath hadm

/-! ## Branch-ready packages from mathlib certificates -/

/-- Branch-seed data is ready for finite Teichmuller generation if the Hensel
part is supplied by the mathlib-facing fixed-level certificate. -/
def BranchSeedMathlibReadyAtLevel (g omega0 p d j r : Nat) : Prop :=
  PrimitiveRootModP g p ∧
    BranchParams p d j ∧
      BranchSeedModP g omega0 p d j ∧
        BranchSeedDerivativeNonzeroModP g p d j ∧
          HenselMathlibCertificateAtLevel g p d j r

/-- Factor-certificate version of the fixed-level mathlib-ready package. -/
def BranchSeedMathlibReadyAtLevelFromFactors (g omega0 p d j r : Nat) : Prop :=
  PrimitiveRootModP g p ∧
    BranchParams p d j ∧
      BranchSeedModP g omega0 p d j ∧
        BranchSeedDerivativeFactorCertificate g p d j ∧
          HenselMathlibCertificateAtLevel g p d j r

/-- All-level mathlib-ready package. -/
def BranchSeedMathlibReadyForAllLevels (g omega0 p d j : Nat) : Prop :=
  PrimitiveRootModP g p ∧
    BranchParams p d j ∧
      BranchSeedModP g omega0 p d j ∧
        BranchSeedDerivativeNonzeroModP g p d j ∧
          HenselMathlibCertificateForAllLevels g p d j

/-- All-level mathlib-ready package using the explicit derivative factor
certificate. -/
def BranchSeedMathlibReadyForAllLevelsFromFactors (g omega0 p d j : Nat) : Prop :=
  PrimitiveRootModP g p ∧
    BranchParams p d j ∧
      BranchSeedModP g omega0 p d j ∧
        BranchSeedDerivativeFactorCertificate g p d j ∧
          HenselMathlibCertificateForAllLevels g p d j

/-- Constructor for the fixed-level mathlib-ready package. -/
theorem branchSeedMathlibReadyAtLevel_intro {g omega0 p d j r : Nat}
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j)
    (hmath : HenselMathlibCertificateAtLevel g p d j r) :
    BranchSeedMathlibReadyAtLevel g omega0 p d j r :=
  ⟨hprim, hparams, hseed, hderiv, hmath⟩

/-- Primitive-root data from the fixed-level mathlib-ready package. -/
theorem branchSeedMathlibReadyAtLevel_primitiveRoot {g omega0 p d j r : Nat}
    (h : BranchSeedMathlibReadyAtLevel g omega0 p d j r) :
    PrimitiveRootModP g p :=
  h.1

/-- Branch parameters from the fixed-level mathlib-ready package. -/
theorem branchSeedMathlibReadyAtLevel_params {g omega0 p d j r : Nat}
    (h : BranchSeedMathlibReadyAtLevel g omega0 p d j r) :
    BranchParams p d j :=
  h.2.1

/-- Seed equality from the fixed-level mathlib-ready package. -/
theorem branchSeedMathlibReadyAtLevel_seed {g omega0 p d j r : Nat}
    (h : BranchSeedMathlibReadyAtLevel g omega0 p d j r) :
    BranchSeedModP g omega0 p d j :=
  h.2.2.1

/-- Derivative nonzero condition from the fixed-level mathlib-ready package. -/
theorem branchSeedMathlibReadyAtLevel_derivative {g omega0 p d j r : Nat}
    (h : BranchSeedMathlibReadyAtLevel g omega0 p d j r) :
    BranchSeedDerivativeNonzeroModP g p d j :=
  h.2.2.2.1

/-- Mathlib-facing Hensel certificate from the fixed-level mathlib-ready package. -/
theorem branchSeedMathlibReadyAtLevel_mathlib {g omega0 p d j r : Nat}
    (h : BranchSeedMathlibReadyAtLevel g omega0 p d j r) :
    HenselMathlibCertificateAtLevel g p d j r :=
  h.2.2.2.2

/-- Convert a fixed-level mathlib-ready package into the existing fixed-level
ready package from Step 21B. -/
theorem branchSeedHenselReadyAtLevel_of_mathlibReadyAtLevel
    {g omega0 p d j r : Nat}
    (h : BranchSeedMathlibReadyAtLevel g omega0 p d j r) :
    BranchSeedHenselReadyAtLevel g omega0 p d j r :=
  branchSeedHenselReadyAtLevel_intro
    (branchSeedMathlibReadyAtLevel_primitiveRoot h)
    (branchSeedMathlibReadyAtLevel_params h)
    (branchSeedMathlibReadyAtLevel_seed h)
    (branchSeedMathlibReadyAtLevel_derivative h)
    (henselSimpleRootExistsUniqueAtLevel_of_mathlibCertificate
      (branchSeedMathlibReadyAtLevel_mathlib h))

/-- Convert a factor-certificate fixed-level mathlib-ready package into the
existing fixed-level ready package from Step 21B. -/
theorem branchSeedHenselReadyAtLevel_of_mathlibReadyAtLevelFromFactors
    {g omega0 p d j r : Nat}
    (h : BranchSeedMathlibReadyAtLevelFromFactors g omega0 p d j r) :
    BranchSeedHenselReadyAtLevel g omega0 p d j r :=
  branchSeedHenselReadyAtLevel_intro
    h.1
    h.2.1
    h.2.2.1
    (branchSeedDerivativeNonzeroModP_of_factorCertificate h.2.2.2.1)
    (henselSimpleRootExistsUniqueAtLevel_of_mathlibCertificate h.2.2.2.2)

/-- Extract a fixed-level mathlib-ready package from the all-level mathlib-ready
package. -/
theorem branchSeedMathlibReadyForAllLevels_at {g omega0 p d j r : Nat}
    (h : BranchSeedMathlibReadyForAllLevels g omega0 p d j)
    (hr_pos : 0 < r) :
    BranchSeedMathlibReadyAtLevel g omega0 p d j r :=
  branchSeedMathlibReadyAtLevel_intro
    h.1
    h.2.1
    h.2.2.1
    h.2.2.2.1
    (henselMathlibCertificateForAllLevels_at h.2.2.2.2 hr_pos)

/-- Extract a fixed-level ready package from an all-level factor-certificate
mathlib-ready package. -/
theorem branchSeedHenselReadyForAllLevelsFromFactors_at_of_mathlibReady
    {g omega0 p d j r : Nat}
    (h : BranchSeedMathlibReadyForAllLevelsFromFactors g omega0 p d j)
    (hr_pos : 0 < r) :
    BranchSeedHenselReadyAtLevel g omega0 p d j r :=
  branchSeedHenselReadyAtLevel_intro
    h.1
    h.2.1
    h.2.2.1
    (branchSeedDerivativeNonzeroModP_of_factorCertificate h.2.2.2.1)
    (henselSimpleRootExistsUniqueAtLevel_of_mathlibCertificate
      (henselMathlibCertificateForAllLevels_at h.2.2.2.2 hr_pos))

/-- Convert the all-level mathlib-ready package into the existing all-level ready
package from Step 21B. -/
theorem branchSeedHenselReadyForAllLevels_of_mathlibReadyForAllLevels
    {g omega0 p d j : Nat}
    (h : BranchSeedMathlibReadyForAllLevels g omega0 p d j) :
    BranchSeedHenselReadyForAllLevels g omega0 p d j :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    henselSimpleRootExistsUniqueForAllLevels_of_mathlibCertificate h.2.2.2.2⟩

/-- Convert the all-level factor-certificate mathlib-ready package into the
existing all-level ready package from Step 21B. -/
theorem branchSeedHenselReadyForAllLevels_of_mathlibReadyForAllLevelsFromFactors
    {g omega0 p d j : Nat}
    (h : BranchSeedMathlibReadyForAllLevelsFromFactors g omega0 p d j) :
    BranchSeedHenselReadyForAllLevels g omega0 p d j :=
  ⟨h.1, h.2.1, h.2.2.1,
    branchSeedDerivativeNonzeroModP_of_factorCertificate h.2.2.2.1,
    henselSimpleRootExistsUniqueForAllLevels_of_mathlibCertificate h.2.2.2.2⟩

/-! ## Consequences: mathlib certificate into finite Teichmuller generation -/

/-- A fixed-level mathlib-ready package produces a finite Teichmuller
representative. -/
theorem teichmullerFiniteExistsAtLevel_of_mathlibReadyAtLevel
    {g omega0 p d j r : Nat}
    (h : BranchSeedMathlibReadyAtLevel g omega0 p d j r) :
    TeichmullerFiniteExistsAtLevel g p d j r :=
  teichmullerFiniteExistsAtLevel_of_branchSeedHenselReadyAtLevel
    (branchSeedHenselReadyAtLevel_of_mathlibReadyAtLevel h)

/-- Factor-certificate version of finite Teichmuller representative production. -/
theorem teichmullerFiniteExistsAtLevel_of_mathlibReadyAtLevelFromFactors
    {g omega0 p d j r : Nat}
    (h : BranchSeedMathlibReadyAtLevelFromFactors g omega0 p d j r) :
    TeichmullerFiniteExistsAtLevel g p d j r :=
  teichmullerFiniteExistsAtLevel_of_branchSeedHenselReadyAtLevel
    (branchSeedHenselReadyAtLevel_of_mathlibReadyAtLevelFromFactors h)

/-- If a positive base has a Hensel-lift witness and the branch is mathlib-ready,
then Core depth at least `r` follows. -/
theorem depthAtLeast_of_branchSeedMathlibReadyAtLevel
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (hready : BranchSeedMathlibReadyAtLevel g omega0 p d j r)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  depthAtLeast_of_branchSeedHenselReadyAtLevel hbase
    (branchSeedHenselReadyAtLevel_of_mathlibReadyAtLevel hready)
    hell_pos

/-- Valuation lower-bound consequence of the fixed-level mathlib-ready package. -/
theorem le_depthValue_of_branchSeedMathlibReadyAtLevel
    {ell g omega0 p d j r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hbase : BaseHasHenselLift ell g p d j r)
    (hready : BranchSeedMathlibReadyAtLevel g omega0 p d j r)
    (hell_pos : 0 < ell) :
    r ≤ depthValue ell p d :=
  le_depthValue_of_branchSeedHenselReadyAtLevel hN hbase
    (branchSeedHenselReadyAtLevel_of_mathlibReadyAtLevel hready)
    hell_pos

/-- Order-side combined consequence of the fixed-level mathlib-ready package. -/
theorem firstWithDepthAtLeast_of_branchSeedMathlibReadyAtLevel
    {ell g omega0 p d j r : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hbase : BaseHasHenselLift ell g p d j r)
    (hready : BranchSeedMathlibReadyAtLevel g omega0 p d j r)
    (hell_pos : 0 < ell) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  firstWithDepthAtLeast_of_branchSeedHenselReadyAtLevel
    hord hd_pos hbase
    (branchSeedHenselReadyAtLevel_of_mathlibReadyAtLevel hready)
    hell_pos

/-- Factor-certificate depth theorem for the mathlib-ready package. -/
theorem depthAtLeast_of_branchSeedMathlibReadyAtLevelFromFactors
    {ell g omega0 p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (hready : BranchSeedMathlibReadyAtLevelFromFactors g omega0 p d j r)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  depthAtLeast_of_branchSeedHenselReadyAtLevel hbase
    (branchSeedHenselReadyAtLevel_of_mathlibReadyAtLevelFromFactors hready)
    hell_pos

/-- Factor-certificate valuation lower-bound theorem for the mathlib-ready
package. -/
theorem le_depthValue_of_branchSeedMathlibReadyAtLevelFromFactors
    {ell g omega0 p d j r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hbase : BaseHasHenselLift ell g p d j r)
    (hready : BranchSeedMathlibReadyAtLevelFromFactors g omega0 p d j r)
    (hell_pos : 0 < ell) :
    r ≤ depthValue ell p d :=
  le_depthValue_of_branchSeedHenselReadyAtLevel hN hbase
    (branchSeedHenselReadyAtLevel_of_mathlibReadyAtLevelFromFactors hready)
    hell_pos

/-- Factor-certificate order-side theorem for the mathlib-ready package. -/
theorem firstWithDepthAtLeast_of_branchSeedMathlibReadyAtLevelFromFactors
    {ell g omega0 p d j r : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hbase : BaseHasHenselLift ell g p d j r)
    (hready : BranchSeedMathlibReadyAtLevelFromFactors g omega0 p d j r)
    (hell_pos : 0 < ell) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  firstWithDepthAtLeast_of_branchSeedHenselReadyAtLevel
    hord hd_pos hbase
    (branchSeedHenselReadyAtLevel_of_mathlibReadyAtLevelFromFactors hready)
    hell_pos

end ApparitionDepth
