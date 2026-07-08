/-
  ABD.ApparitionDepth3.HenselAlgebra

  First layer of the organic Hensel block.

  This file contains only the residue-level language used by finite Hensel:
    * a seed-compatible lift at level r;
    * existence-and-uniqueness at level r;
    * small projections from lift data.

  It deliberately does not mention apparition depth.  Depth belongs to the
  `RootAtLevel <-> DepthAtLeast` bridge, not to Hensel itself.
-/

import ABD.ApparitionDepth3.SimpleRoot

namespace ApparitionDepth3

/-- A lift at precision `p^r` staying on the same seed modulo `p`.

This is the basic Hensel object: the representative still lies above the original
seed modulo `p`, and it is already a root of `X^d - 1` modulo `p^r`. -/
def LiftAtLevel (seed omega p d r : Nat) : Prop :=
  BranchSeedModP seed omega p ∧ RootAtLevel omega p d r

/-- Existence and uniqueness of a seed-compatible lift at level `r`.

Uniqueness is stated as equality in `ZMod (p^r)`, not equality of natural-number
representatives. -/
def ExistsUniqueLiftAtLevel (seed p d r : Nat) : Prop :=
  ∃ omega : Nat,
    LiftAtLevel seed omega p d r ∧
      ∀ omega' : Nat,
        LiftAtLevel seed omega' p d r →
          (omega' : ZMod (p ^ r)) = (omega : ZMod (p ^ r))

/-- A lift gives the root statement at the same level. -/
theorem rootAtLevel_of_liftAtLevel {seed omega p d r : Nat}
    (hlift : LiftAtLevel seed omega p d r) :
    RootAtLevel omega p d r :=
  hlift.2

/-- A lift remembers its seed congruence modulo `p`. -/
theorem seedCongr_of_liftAtLevel {seed omega p d r : Nat}
    (hlift : LiftAtLevel seed omega p d r) :
    BranchSeedModP seed omega p :=
  hlift.1

/-- Build a lift from seed congruence and root-at-level data. -/
theorem liftAtLevel_intro {seed omega p d r : Nat}
    (hseed : BranchSeedModP seed omega p)
    (hroot : RootAtLevel omega p d r) :
    LiftAtLevel seed omega p d r :=
  ⟨hseed, hroot⟩

end ApparitionDepth3
