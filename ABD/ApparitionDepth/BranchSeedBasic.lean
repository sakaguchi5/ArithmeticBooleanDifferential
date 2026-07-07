/-
  ABD.ApparitionDepth.BranchSeedBasic

  Step 14 of the Apparition-Depth Decomposition project.

  This file is a light helper layer for the finite branch seed formula introduced
  in `TeichmullerBranch`:

      omega ≡ g ^ (((p - 1) / d) * j)  mod p.

  It does not yet assert that `g` is a primitive root, and it does not yet prove
  that the seed is a `d`-th root.  Those are the next layers.  The goal here is
  only to make the seed formula easy to rewrite, project, and package.
-/

import ABD.ApparitionDepth.TeichmullerBranch

namespace ApparitionDepth

/-! ## Seed exponent and seed value -/

/-- The exponent used for the branch seed attached to `(p,d,j)`. -/
def branchSeedExponent (p d j : Nat) : Nat :=
  ((p - 1) / d) * j

/-- The residue-class value of the branch seed in `ZMod p`, generated from `g`. -/
def branchSeedValue (g p d j : Nat) : ZMod p :=
  (g : ZMod p) ^ branchSeedExponent p d j

/-- Unfolding helper for the branch seed exponent. -/
theorem branchSeedExponent_def (p d j : Nat) :
    branchSeedExponent p d j = ((p - 1) / d) * j :=
  rfl

/-- Unfolding helper for the branch seed value. -/
theorem branchSeedValue_def (g p d j : Nat) :
    branchSeedValue g p d j =
      ((g : ZMod p) ^ (((p - 1) / d) * j)) :=
  rfl

/-- `BranchSeedModP` is exactly equality with `branchSeedValue`. -/
theorem branchSeedModP_iff_seedValue {g omega p d j : Nat} :
    BranchSeedModP g omega p d j ↔
      (omega : ZMod p) = branchSeedValue g p d j := by
  unfold BranchSeedModP branchSeedValue branchSeedExponent
  rfl

/-- Constructor form for `BranchSeedModP` using `branchSeedValue`. -/
theorem branchSeedModP_intro {g omega p d j : Nat}
    (h : (omega : ZMod p) = branchSeedValue g p d j) :
    BranchSeedModP g omega p d j :=
  (branchSeedModP_iff_seedValue (g := g) (omega := omega) (p := p) (d := d) (j := j)).mpr h

/-- Projection form for `BranchSeedModP` using `branchSeedValue`. -/
theorem branchSeedModP_seedValue {g omega p d j : Nat}
    (h : BranchSeedModP g omega p d j) :
    (omega : ZMod p) = branchSeedValue g p d j :=
  (branchSeedModP_iff_seedValue (g := g) (omega := omega) (p := p) (d := d) (j := j)).mp h

/-- Transport a seed statement along equality of representatives modulo `p`. -/
theorem branchSeedModP_of_zmod_eq {g omega omega' p d j : Nat}
    (homega : (omega : ZMod p) = (omega' : ZMod p))
    (hseed : BranchSeedModP g omega p d j) :
    BranchSeedModP g omega' p d j := by
  unfold BranchSeedModP at *
  rw [← homega]
  exact hseed

/-- Symmetric transport form for seed representatives. -/
theorem branchSeedModP_of_zmod_eq_left {g omega omega' p d j : Nat}
    (homega : (omega' : ZMod p) = (omega : ZMod p))
    (hseed : BranchSeedModP g omega p d j) :
    BranchSeedModP g omega' p d j :=
  branchSeedModP_of_zmod_eq (homega := homega.symm) hseed

/-! ## Small consequences of branch parameters -/

/-- The order parameter `d` is positive under `BranchParams`. -/
theorem branchParams_d_pos {p d j : Nat}
    (h : BranchParams p d j) :
    0 < d :=
  branchIndex_pos (branchParams_index h)

/-- The branch index `j` is positive under `BranchParams`. -/
theorem branchParams_j_pos {p d j : Nat}
    (h : BranchParams p d j) :
    0 < j :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (branchIndex_one_le (branchParams_index h))

/-- The branch index `j` is coprime to `d` under `BranchParams`. -/
theorem branchParams_j_coprime_d {p d j : Nat}
    (h : BranchParams p d j) :
    j.Coprime d :=
  branchIndex_coprime (branchParams_index h)

/-! ## Packaging helpers for finite-level omega branches -/

/-- A seed together with a root condition at level `p^r`. -/
def SeededRootAtLevel (g omega p d j r : Nat) : Prop :=
  BranchSeedModP g omega p d j ∧ OmegaRootAtLevel omega p d r

/-- Projection: a seeded root has the expected seed modulo `p`. -/
theorem seededRootAtLevel_seed {g omega p d j r : Nat}
    (h : SeededRootAtLevel g omega p d j r) :
    BranchSeedModP g omega p d j :=
  h.1

/-- Projection: a seeded root is a root at level `p^r`. -/
theorem seededRootAtLevel_root {g omega p d j r : Nat}
    (h : SeededRootAtLevel g omega p d j r) :
    OmegaRootAtLevel omega p d r :=
  h.2

/-- Constructor for `SeededRootAtLevel`. -/
theorem seededRootAtLevel_intro {g omega p d j r : Nat}
    (hseed : BranchSeedModP g omega p d j)
    (hroot : OmegaRootAtLevel omega p d r) :
    SeededRootAtLevel g omega p d j r :=
  ⟨hseed, hroot⟩

/-- Reassociate `OmegaBranchAtLevel` as parameters plus a seeded root. -/
theorem omegaBranchAtLevel_iff_params_seededRoot {g omega p d j r : Nat} :
    OmegaBranchAtLevel g omega p d j r ↔
      BranchParams p d j ∧ SeededRootAtLevel g omega p d j r := by
  constructor
  · intro h
    exact ⟨omegaBranchAtLevel_params h,
      ⟨omegaBranchAtLevel_seed h, omegaBranchAtLevel_root h⟩⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2⟩

/-- Constructor for `OmegaBranchAtLevel`. -/
theorem omegaBranchAtLevel_intro {g omega p d j r : Nat}
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega p d j)
    (hroot : OmegaRootAtLevel omega p d r) :
    OmegaBranchAtLevel g omega p d j r :=
  ⟨hparams, hseed, hroot⟩

/-- Constructor for the existential omega representative. -/
theorem omegaRepresentative_intro {g omega p d j r : Nat}
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega p d j)
    (hroot : OmegaRootAtLevel omega p d r) :
    OmegaRepresentative omega p d j r :=
  ⟨g, omegaBranchAtLevel_intro hparams hseed hroot⟩

/-- Constructor for branch membership of a base. -/
theorem baseInOmegaBranch_intro {ell omega p d j r : Nat}
    (hcongr : (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)))
    (homega : OmegaRepresentative omega p d j r) :
    BaseInOmegaBranch ell omega p d j r :=
  ⟨hcongr, homega⟩

/-- Direct constructor from a generator, branch data, and residue equality. -/
theorem baseInOmegaBranch_intro_of_seed_root {ell g omega p d j r : Nat}
    (hcongr : (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)))
    (hparams : BranchParams p d j)
    (hseed : BranchSeedModP g omega p d j)
    (hroot : OmegaRootAtLevel omega p d r) :
    BaseInOmegaBranch ell omega p d j r :=
  baseInOmegaBranch_intro hcongr
    (omegaRepresentative_intro (g := g) hparams hseed hroot)

end ApparitionDepth
