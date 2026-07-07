/-
  ABD.ApparitionDepth.HenselUniquenessProofInterface

  Step 20B of the Apparition-Depth Decomposition project.

  This file connects the simple-root input from `HenselDerivativeCondition` to the
  finite-level uniqueness interface from `HenselLiftUniqueness`.

  Important design choice:
    this is still not the heavy algebraic proof of Hensel uniqueness.  Instead it
    isolates the exact theorem-shape that such a proof must provide:

      a level-one admissible simple root implies uniqueness of all lifts at level r.

  Once that theorem-shape is supplied, the existing canonical-representative and
  AD-depth transport machinery becomes available immediately.
-/

import ABD.ApparitionDepth.HenselDerivativeCondition

namespace ApparitionDepth

/-! ## Simple-root uniqueness theorem shape -/

/-- Hensel uniqueness at a fixed finite level, supplied from a level-one simple
root datum.

For the polynomial `X^d - 1`, the intended future proof is:

* the branch seed is a simple root modulo `p`;
* therefore its lift to level `p^r` is unique.

This predicate records exactly that theorem-shape without pretending that the
heavy Hensel argument has already been proved. -/
def HenselSimpleRootUniquenessAtLevel (g p d j r : Nat) : Prop :=
  ∀ omega0 : Nat,
    HenselAdmissibleLiftAtLevelOne g omega0 p d j →
      HenselLiftUniqueAtLevel g p d j r

/-- Hensel uniqueness at every positive finite level, from the same level-one
simple-root datum. -/
def HenselSimpleRootUniquenessForAllLevels (g p d j : Nat) : Prop :=
  ∀ r : Nat, 0 < r → HenselSimpleRootUniquenessAtLevel g p d j r

/-! ## Constructors and projections -/

/-- Constructor for fixed-level simple-root uniqueness. -/
theorem henselSimpleRootUniquenessAtLevel_intro {g p d j r : Nat}
    (h : ∀ omega0 : Nat,
      HenselAdmissibleLiftAtLevelOne g omega0 p d j →
        HenselLiftUniqueAtLevel g p d j r) :
    HenselSimpleRootUniquenessAtLevel g p d j r :=
  h

/-- Apply fixed-level simple-root uniqueness to a level-one admissible lift. -/
theorem henselSimpleRootUniquenessAtLevel_apply
    {g omega0 p d j r : Nat}
    (huniq : HenselSimpleRootUniquenessAtLevel g p d j r)
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j) :
    HenselLiftUniqueAtLevel g p d j r :=
  huniq omega0 hadm

/-- Extract fixed-level simple-root uniqueness from the all-level version. -/
theorem henselSimpleRootUniquenessForAllLevels_at
    {g p d j r : Nat}
    (huniq : HenselSimpleRootUniquenessForAllLevels g p d j)
    (hr_pos : 0 < r) :
    HenselSimpleRootUniquenessAtLevel g p d j r :=
  huniq r hr_pos

/-- A level-one admissible lift plus all-level simple-root uniqueness gives the
existing all-level uniqueness interface. -/
theorem henselLiftUniqueForAllLevels_of_simpleRootUniquenessForAllLevels
    {g omega0 p d j : Nat}
    (huniq : HenselSimpleRootUniquenessForAllLevels g p d j)
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j) :
    HenselLiftUniqueForAllLevels g p d j :=
  fun _r hr_pos =>
    henselSimpleRootUniquenessAtLevel_apply
      (henselSimpleRootUniquenessForAllLevels_at huniq hr_pos)
      hadm

/-! ## Branch-seed specialization -/

/-- Primitive-root seed data plus the derivative condition provides the
level-one admissible input required by fixed-level simple-root uniqueness. -/
theorem henselLiftUniqueAtLevel_of_branchSeed_of_primitiveRoot_derivative
    {g omega0 p d j r : Nat}
    (huniq : HenselSimpleRootUniquenessAtLevel g p d j r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    HenselLiftUniqueAtLevel g p d j r :=
  henselSimpleRootUniquenessAtLevel_apply huniq
    (henselAdmissibleLiftAtLevelOne_of_branchSeed_of_primitiveRoot_derivative
      hprim hparams hseed hderiv)

/-- All-level version of the previous theorem. -/
theorem henselLiftUniqueForAllLevels_of_branchSeed_of_primitiveRoot_derivative
    {g omega0 p d j : Nat}
    (huniq : HenselSimpleRootUniquenessForAllLevels g p d j)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    HenselLiftUniqueForAllLevels g p d j :=
  henselLiftUniqueForAllLevels_of_simpleRootUniquenessForAllLevels huniq
    (henselAdmissibleLiftAtLevelOne_of_branchSeed_of_primitiveRoot_derivative
      hprim hparams hseed hderiv)

/-! ## Canonical representatives from the uniqueness theorem-shape -/

/-- A concrete lift becomes canonical once fixed-level simple-root uniqueness is
available. -/
theorem henselLiftCanonicalRep_of_lift_of_simpleRootUniquenessAtLevel
    {omega omega0 g p d j r : Nat}
    (huniq : HenselSimpleRootUniquenessAtLevel g p d j r)
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j)
    (hlift : HenselBranchLiftAtLevel g omega p d j r) :
    HenselLiftCanonicalRep omega g p d j r :=
  henselLiftCanonicalRep_intro hlift
    (henselSimpleRootUniquenessAtLevel_apply huniq hadm)

/-- Branch-seed primitive-root form of canonicality for a concrete lift. -/
theorem henselLiftCanonicalRep_of_lift_of_branchSeed_primitiveRoot_derivative
    {omega omega0 g p d j r : Nat}
    (huniq : HenselSimpleRootUniquenessAtLevel g p d j r)
    (hlift : HenselBranchLiftAtLevel g omega p d j r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    HenselLiftCanonicalRep omega g p d j r :=
  henselLiftCanonicalRep_of_lift_of_simpleRootUniquenessAtLevel huniq
    (henselAdmissibleLiftAtLevelOne_of_branchSeed_of_primitiveRoot_derivative
      hprim hparams hseed hderiv)
    hlift

end ApparitionDepth
