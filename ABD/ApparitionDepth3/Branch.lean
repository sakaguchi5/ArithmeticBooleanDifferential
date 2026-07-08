/-
  ABD.ApparitionDepth3.Branch

  Organic branch layer.
  Instead of replaying the old primitive-root bridge as many files, this layer
  exposes exactly the data later Hensel/cyclotomic/carry modules need:
    * a branch seed;
    * seed congruence for a concrete representative;
    * seed root modulo p;
    * finite branch membership.
-/

import ABD.ApparitionDepth3.Order

namespace ApparitionDepth3

/-- Branch index: `1 <= j <= d` and `gcd j d = 1`. -/
def BranchIndex (d j : Nat) : Prop :=
  1 ≤ j ∧ j ≤ d ∧ Nat.Coprime j d

/-- Branch parameters: `d | p-1`, plus a branch index `j`. -/
def BranchParams (p d j : Nat) : Prop :=
  d ∣ p - 1 ∧ BranchIndex d j

theorem branchParams_dvd {p d j : Nat} (h : BranchParams p d j) : d ∣ p - 1 :=
  h.1

theorem branchParams_index {p d j : Nat} (h : BranchParams p d j) : BranchIndex d j :=
  h.2

theorem branchParams_j_pos {p d j : Nat} (h : BranchParams p d j) : 0 < j :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one h.2.1

theorem branchParams_d_pos {p d j : Nat} (h : BranchParams p d j) : 0 < d :=
  Nat.lt_of_lt_of_le (branchParams_j_pos h) h.2.2.1

/-- Seed congruence modulo `p`. -/
def BranchSeedModP (seed omega p : Nat) : Prop :=
  (omega : ZMod p) = (seed : ZMod p)

/-- A finite branch representative: same seed modulo `p`, and root at level `r`. -/
def BranchAtLevel (seed omega p d r : Nat) : Prop :=
  BranchSeedModP seed omega p ∧ RootAtLevel omega p d r

/-- A base lies in a generated branch at level `r`. -/
def BaseInBranchAtLevel (ell seed omega p d r : Nat) : Prop :=
  (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) ∧
    BranchAtLevel seed omega p d r

/-- A root at level one packaged as branch seed data. -/
def SeedRootModP (seed p d : Nat) : Prop :=
  RootAtLevel seed p d 1

/-- Transport root status from a branch representative to a base in the same class. -/
theorem rootAtLevel_of_baseInBranchAtLevel {ell seed omega p d r : Nat}
    (h : BaseInBranchAtLevel ell seed omega p d r) :
    RootAtLevel ell p d r := by
  unfold BaseInBranchAtLevel BranchAtLevel at h
  simpa [RootAtLevel, h.1] using h.2.2

/-- A positive base in a branch has depth at least `r`. -/
theorem depthAtLeast_of_baseInBranchAtLevel_of_base_pos
    {ell seed omega p d r : Nat}
    (h : BaseInBranchAtLevel ell seed omega p d r)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  depthAtLeast_of_rootAtLevel_of_base_pos hell_pos
    (rootAtLevel_of_baseInBranchAtLevel h)

/-- Transport a seed root mod p to level 1 of its branch representative. -/
theorem rootAtLevel_one_of_seedRoot_of_seedCongr
    {seed omega p d : Nat}
    (hroot : SeedRootModP seed p d)
    (hseed : BranchSeedModP seed omega p) :
    RootAtLevel omega p d 1 := by
  unfold SeedRootModP at hroot
  unfold BranchSeedModP at hseed
  unfold RootAtLevel at hroot ⊢
  rw [levelOneModulus_eq p] at hroot ⊢
  rw [hseed]
  exact hroot

/-- Build a level-one branch from seed root and seed congruence. -/
theorem branchAtLevel_one_of_seedRoot
    {seed omega p d : Nat}
    (hroot : SeedRootModP seed p d)
    (hseed : BranchSeedModP seed omega p) :
    BranchAtLevel seed omega p d 1 :=
  ⟨hseed, rootAtLevel_one_of_seedRoot_of_seedCongr hroot hseed⟩

end ApparitionDepth3
