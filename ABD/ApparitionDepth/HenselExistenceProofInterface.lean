/-
  ABD.ApparitionDepth.HenselExistenceProofInterface

  Step 20C of the Apparition-Depth Decomposition project.

  This file connects the simple-root input from Step 20A and the uniqueness
  theorem-shape from Step 20B to the existing finite-level existence and
  exists-unique Hensel interfaces.

  Important design choice:
    this is not yet the heavy Hensel existence theorem.  It isolates the precise
    theorem-shape that such a proof should provide, and proves all consequences
    once that theorem-shape is available.
-/

import ABD.ApparitionDepth.HenselUniquenessProofInterface

namespace ApparitionDepth

/-! ## Simple-root existence theorem shape -/

/-- Hensel existence at a fixed finite level, supplied from a level-one simple
root datum. -/
def HenselSimpleRootExistenceAtLevel (g p d j r : Nat) : Prop :=
  ∀ omega0 : Nat,
    HenselAdmissibleLiftAtLevelOne g omega0 p d j →
      HenselLiftExists g p d j r

/-- Hensel existence at every positive finite level, from the same level-one
simple-root datum. -/
def HenselSimpleRootExistenceForAllLevels (g p d j : Nat) : Prop :=
  ∀ r : Nat, 0 < r → HenselSimpleRootExistenceAtLevel g p d j r

/-- Fixed-level simple-root existence and uniqueness bundled together. -/
def HenselSimpleRootExistsUniqueAtLevel (g p d j r : Nat) : Prop :=
  HenselSimpleRootExistenceAtLevel g p d j r ∧
    HenselSimpleRootUniquenessAtLevel g p d j r

/-- All-level simple-root existence and uniqueness bundled together. -/
def HenselSimpleRootExistsUniqueForAllLevels (g p d j : Nat) : Prop :=
  ∀ r : Nat, 0 < r → HenselSimpleRootExistsUniqueAtLevel g p d j r

/-- Existing finite-level Hensel existence and uniqueness at every positive level. -/
def HenselLiftExistsUniqueForAllLevels (g p d j : Nat) : Prop :=
  ∀ r : Nat, 0 < r → HenselLiftExistsUnique g p d j r

/-! ## Constructors and projections -/

/-- Constructor for fixed-level simple-root existence. -/
theorem henselSimpleRootExistenceAtLevel_intro {g p d j r : Nat}
    (h : ∀ omega0 : Nat,
      HenselAdmissibleLiftAtLevelOne g omega0 p d j →
        HenselLiftExists g p d j r) :
    HenselSimpleRootExistenceAtLevel g p d j r :=
  h

/-- Apply fixed-level simple-root existence to a level-one admissible lift. -/
theorem henselSimpleRootExistenceAtLevel_apply
    {g omega0 p d j r : Nat}
    (hexists : HenselSimpleRootExistenceAtLevel g p d j r)
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j) :
    HenselLiftExists g p d j r :=
  hexists omega0 hadm

/-- Extract fixed-level simple-root existence from the all-level version. -/
theorem henselSimpleRootExistenceForAllLevels_at
    {g p d j r : Nat}
    (hexists : HenselSimpleRootExistenceForAllLevels g p d j)
    (hr_pos : 0 < r) :
    HenselSimpleRootExistenceAtLevel g p d j r :=
  hexists r hr_pos

/-- Projection: simple-root existence from bundled simple-root exists-unique. -/
theorem henselSimpleRootExistsUniqueAtLevel_exists {g p d j r : Nat}
    (h : HenselSimpleRootExistsUniqueAtLevel g p d j r) :
    HenselSimpleRootExistenceAtLevel g p d j r :=
  h.1

/-- Projection: simple-root uniqueness from bundled simple-root exists-unique. -/
theorem henselSimpleRootExistsUniqueAtLevel_unique {g p d j r : Nat}
    (h : HenselSimpleRootExistsUniqueAtLevel g p d j r) :
    HenselSimpleRootUniquenessAtLevel g p d j r :=
  h.2

/-- Extract fixed-level simple-root exists-unique from the all-level version. -/
theorem henselSimpleRootExistsUniqueForAllLevels_at
    {g p d j r : Nat}
    (h : HenselSimpleRootExistsUniqueForAllLevels g p d j)
    (hr_pos : 0 < r) :
    HenselSimpleRootExistsUniqueAtLevel g p d j r :=
  h r hr_pos

/-! ## Transport to the existing Hensel interfaces -/

/-- A level-one admissible lift plus simple-root existence gives the existing
`HenselLiftExists` interface. -/
theorem henselLiftExists_of_simpleRootExistenceAtLevel
    {g omega0 p d j r : Nat}
    (hexists : HenselSimpleRootExistenceAtLevel g p d j r)
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j) :
    HenselLiftExists g p d j r :=
  henselSimpleRootExistenceAtLevel_apply hexists hadm

/-- A level-one admissible lift plus all-level simple-root existence gives the
existing all-level existence interface. -/
theorem henselLiftExistsForAllLevels_of_simpleRootExistenceForAllLevels
    {g omega0 p d j : Nat}
    (hexists : HenselSimpleRootExistenceForAllLevels g p d j)
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j) :
    HenselLiftExistsForAllLevels g p d j :=
  fun _r hr_pos =>
    henselLiftExists_of_simpleRootExistenceAtLevel
      (henselSimpleRootExistenceForAllLevels_at hexists hr_pos)
      hadm

/-- Fixed-level simple-root exists-unique gives the existing fixed-level
`HenselLiftExistsUnique` interface. -/
theorem henselLiftExistsUnique_of_simpleRootExistsUniqueAtLevel
    {g omega0 p d j r : Nat}
    (h : HenselSimpleRootExistsUniqueAtLevel g p d j r)
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j) :
    HenselLiftExistsUnique g p d j r :=
  henselLiftExistsUnique_intro
    (henselLiftExists_of_simpleRootExistenceAtLevel
      (henselSimpleRootExistsUniqueAtLevel_exists h) hadm)
    (henselSimpleRootUniquenessAtLevel_apply
      (henselSimpleRootExistsUniqueAtLevel_unique h) hadm)

/-- All-level simple-root exists-unique gives the existing all-level
exists-unique interface. -/
theorem henselLiftExistsUniqueForAllLevels_of_simpleRootExistsUniqueForAllLevels
    {g omega0 p d j : Nat}
    (h : HenselSimpleRootExistsUniqueForAllLevels g p d j)
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j) :
    HenselLiftExistsUniqueForAllLevels g p d j :=
  fun _r hr_pos =>
    henselLiftExistsUnique_of_simpleRootExistsUniqueAtLevel
      (henselSimpleRootExistsUniqueForAllLevels_at h hr_pos)
      hadm

/-! ## Branch-seed specialization -/

/-- Primitive-root seed data plus derivative nonvanishing turns fixed-level
simple-root existence into `HenselLiftExists`. -/
theorem henselLiftExists_of_branchSeed_of_primitiveRoot_derivative
    {g omega0 p d j r : Nat}
    (hexists : HenselSimpleRootExistenceAtLevel g p d j r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    HenselLiftExists g p d j r :=
  henselLiftExists_of_simpleRootExistenceAtLevel hexists
    (henselAdmissibleLiftAtLevelOne_of_branchSeed_of_primitiveRoot_derivative
      hprim hparams hseed hderiv)

/-- Primitive-root seed data plus derivative nonvanishing turns fixed-level
simple-root exists-unique into `HenselLiftExistsUnique`. -/
theorem henselLiftExistsUnique_of_branchSeed_of_primitiveRoot_derivative
    {g omega0 p d j r : Nat}
    (h : HenselSimpleRootExistsUniqueAtLevel g p d j r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    HenselLiftExistsUnique g p d j r :=
  henselLiftExistsUnique_of_simpleRootExistsUniqueAtLevel h
    (henselAdmissibleLiftAtLevelOne_of_branchSeed_of_primitiveRoot_derivative
      hprim hparams hseed hderiv)

/-! ## Canonical representative consequences -/

/-- Fixed-level simple-root exists-unique produces a canonical representative. -/
theorem exists_henselLiftCanonicalRep_of_simpleRootExistsUniqueAtLevel
    {g omega0 p d j r : Nat}
    (h : HenselSimpleRootExistsUniqueAtLevel g p d j r)
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j) :
    ∃ omega : Nat, HenselLiftCanonicalRep omega g p d j r :=
  exists_henselLiftCanonicalRep_of_existsUnique
    (henselLiftExistsUnique_of_simpleRootExistsUniqueAtLevel h hadm)

/-- Branch-seed primitive-root form of canonical representative existence. -/
theorem exists_henselLiftCanonicalRep_of_branchSeed_primitiveRoot_derivative
    {g omega0 p d j r : Nat}
    (h : HenselSimpleRootExistsUniqueAtLevel g p d j r)
    (hprim : PrimitiveRootModP g p)
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega0 p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    ∃ omega : Nat, HenselLiftCanonicalRep omega g p d j r :=
  exists_henselLiftCanonicalRep_of_simpleRootExistsUniqueAtLevel h
    (henselAdmissibleLiftAtLevelOne_of_branchSeed_of_primitiveRoot_derivative
      hprim hparams hseed hderiv)

/-- Fixed-level simple-root existence gives existence of an omega representative. -/
theorem omegaRepresentative_exists_of_simpleRootExistenceAtLevel
    {g omega0 p d j r : Nat}
    (hexists : HenselSimpleRootExistenceAtLevel g p d j r)
    (hadm : HenselAdmissibleLiftAtLevelOne g omega0 p d j) :
    ∃ omega : Nat, OmegaRepresentative omega p d j r :=
  omegaRepresentative_exists_of_henselLiftExists
    (henselLiftExists_of_simpleRootExistenceAtLevel hexists hadm)

end ApparitionDepth
