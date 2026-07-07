/-
  ABD.ApparitionDepth.HenselLiftUniqueness

  Step 19 of the Apparition-Depth Decomposition project.

  This file introduces the finite-level uniqueness interface for Hensel lifts.

  Important design choice:
    this is still not the heavy Hensel uniqueness theorem from algebra.  Instead,
    it names the uniqueness statement at a finite level and proves the transport
    consequences once such a uniqueness certificate is available.

  The intended statement is:

      two lifts of the same branch seed to level p^r are equal in ZMod (p^r).

  Once this is available, any base known to be congruent to some lift can be
  transported to a chosen canonical lift representative.
-/

import ABD.ApparitionDepth.HenselLiftExistence

namespace ApparitionDepth

/-! ## Finite-level uniqueness predicates -/

/-- Uniqueness of the Hensel lift at a fixed finite level.

Two branch lifts of the same `(g,p,d,j)` data at level `r` are equal as residue
classes modulo `p^r`.  This is the finite-level uniqueness statement expected
from Hensel's lemma. -/
def HenselLiftUniqueAtLevel (g p d j r : Nat) : Prop :=
  ∀ omega₁ omega₂ : Nat,
    HenselBranchLiftAtLevel g omega₁ p d j r →
    HenselBranchLiftAtLevel g omega₂ p d j r →
    (omega₁ : ZMod (p ^ r)) = (omega₂ : ZMod (p ^ r))

/-- Uniqueness of Hensel lifts at every positive finite level. -/
def HenselLiftUniqueForAllLevels (g p d j : Nat) : Prop :=
  ∀ r : Nat, 0 < r → HenselLiftUniqueAtLevel g p d j r

/-- Existence and uniqueness of the Hensel lift at a fixed finite level. -/
def HenselLiftExistsUnique (g p d j r : Nat) : Prop :=
  HenselLiftExists g p d j r ∧ HenselLiftUniqueAtLevel g p d j r

/-- A chosen representative is canonical at level `p^r` if it is a lift and all
other lifts are congruent to it modulo `p^r`. -/
def HenselLiftCanonicalRep (omega g p d j r : Nat) : Prop :=
  HenselBranchLiftAtLevel g omega p d j r ∧ HenselLiftUniqueAtLevel g p d j r

/-! ## Constructors and projections -/

/-- Constructor for finite-level uniqueness. -/
theorem henselLiftUniqueAtLevel_intro {g p d j r : Nat}
    (h : ∀ omega₁ omega₂ : Nat,
      HenselBranchLiftAtLevel g omega₁ p d j r →
      HenselBranchLiftAtLevel g omega₂ p d j r →
      (omega₁ : ZMod (p ^ r)) = (omega₂ : ZMod (p ^ r))) :
    HenselLiftUniqueAtLevel g p d j r :=
  h

/-- Apply a finite-level uniqueness certificate. -/
theorem henselLiftUniqueAtLevel_apply {g p d j r omega₁ omega₂ : Nat}
    (huniq : HenselLiftUniqueAtLevel g p d j r)
    (h₁ : HenselBranchLiftAtLevel g omega₁ p d j r)
    (h₂ : HenselBranchLiftAtLevel g omega₂ p d j r) :
    (omega₁ : ZMod (p ^ r)) = (omega₂ : ZMod (p ^ r)) :=
  huniq omega₁ omega₂ h₁ h₂

/-- Extract the level-`r` uniqueness statement from all-level uniqueness. -/
theorem henselLiftUniqueForAllLevels_at {g p d j r : Nat}
    (huniq : HenselLiftUniqueForAllLevels g p d j)
    (hr_pos : 0 < r) :
    HenselLiftUniqueAtLevel g p d j r :=
  huniq r hr_pos

/-- Constructor for existence plus uniqueness. -/
theorem henselLiftExistsUnique_intro {g p d j r : Nat}
    (hexists : HenselLiftExists g p d j r)
    (huniq : HenselLiftUniqueAtLevel g p d j r) :
    HenselLiftExistsUnique g p d j r :=
  ⟨hexists, huniq⟩

/-- Projection: existence from existence plus uniqueness. -/
theorem henselLiftExistsUnique_exists {g p d j r : Nat}
    (h : HenselLiftExistsUnique g p d j r) :
    HenselLiftExists g p d j r :=
  h.1

/-- Projection: uniqueness from existence plus uniqueness. -/
theorem henselLiftExistsUnique_unique {g p d j r : Nat}
    (h : HenselLiftExistsUnique g p d j r) :
    HenselLiftUniqueAtLevel g p d j r :=
  h.2

/-- Constructor for a canonical representative. -/
theorem henselLiftCanonicalRep_intro {omega g p d j r : Nat}
    (hlift : HenselBranchLiftAtLevel g omega p d j r)
    (huniq : HenselLiftUniqueAtLevel g p d j r) :
    HenselLiftCanonicalRep omega g p d j r :=
  ⟨hlift, huniq⟩

/-- Projection: the canonical representative is a Hensel lift. -/
theorem henselLiftCanonicalRep_lift {omega g p d j r : Nat}
    (h : HenselLiftCanonicalRep omega g p d j r) :
    HenselBranchLiftAtLevel g omega p d j r :=
  h.1

/-- Projection: a canonical representative carries the uniqueness certificate. -/
theorem henselLiftCanonicalRep_unique {omega g p d j r : Nat}
    (h : HenselLiftCanonicalRep omega g p d j r) :
    HenselLiftUniqueAtLevel g p d j r :=
  h.2

/-- Existence plus uniqueness produces some canonical representative. -/
theorem exists_henselLiftCanonicalRep_of_existsUnique {g p d j r : Nat}
    (h : HenselLiftExistsUnique g p d j r) :
    ∃ omega : Nat, HenselLiftCanonicalRep omega g p d j r := by
  rcases henselLiftExistsUnique_exists h with ⟨omega, hlift⟩
  exact ⟨omega, henselLiftCanonicalRep_intro hlift (henselLiftExistsUnique_unique h)⟩

/-! ## Transport through uniqueness -/

/-- Any lift is congruent to a chosen canonical representative modulo `p^r`. -/
theorem zmod_eq_of_henselLiftCanonicalRep {omega omega' g p d j r : Nat}
    (hcanon : HenselLiftCanonicalRep omega g p d j r)
    (hlift : HenselBranchLiftAtLevel g omega' p d j r) :
    (omega' : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) :=
  henselLiftUniqueAtLevel_apply
    (henselLiftCanonicalRep_unique hcanon)
    hlift
    (henselLiftCanonicalRep_lift hcanon)

/-- Two explicit lift witnesses are congruent modulo `p^r` under uniqueness. -/
theorem zmod_eq_of_two_henselBranchLiftAtLevel {omega₁ omega₂ g p d j r : Nat}
    (huniq : HenselLiftUniqueAtLevel g p d j r)
    (h₁ : HenselBranchLiftAtLevel g omega₁ p d j r)
    (h₂ : HenselBranchLiftAtLevel g omega₂ p d j r) :
    (omega₁ : ZMod (p ^ r)) = (omega₂ : ZMod (p ^ r)) :=
  henselLiftUniqueAtLevel_apply huniq h₁ h₂

/-- If a base is congruent to some Hensel lift, then it is congruent to any chosen
canonical representative of the same branch. -/
theorem baseHasHenselLift_congr_to_canonical
    {ell omega g p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (hcanon : HenselLiftCanonicalRep omega g p d j r) :
    (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) := by
  rcases hbase with ⟨omega', hcongr, hlift'⟩
  calc
    (ell : ZMod (p ^ r)) = (omega' : ZMod (p ^ r)) := hcongr
    _ = (omega : ZMod (p ^ r)) := zmod_eq_of_henselLiftCanonicalRep hcanon hlift'

/-- A base with some Hensel-lift witness lies in the omega branch of a canonical
representative. -/
theorem baseInOmegaBranch_of_baseHasHenselLift_canonical
    {ell omega g p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (hcanon : HenselLiftCanonicalRep omega g p d j r) :
    BaseInOmegaBranch ell omega p d j r :=
  baseInOmegaBranch_of_henselBranchLiftAtLevel
    (baseHasHenselLift_congr_to_canonical hbase hcanon)
    (henselLiftCanonicalRep_lift hcanon)

/-- Therefore, if a positive base is congruent to some Hensel lift, then it has
Core depth at least `r`, using a canonical representative. -/
theorem depthAtLeast_of_baseHasHenselLift_canonical_of_base_pos
    {ell omega g p d j r : Nat}
    (hbase : BaseHasHenselLift ell g p d j r)
    (hcanon : HenselLiftCanonicalRep omega g p d j r)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  depthAtLeast_of_baseInOmegaBranch_of_base_pos
    (baseInOmegaBranch_of_baseHasHenselLift_canonical hbase hcanon)
    hell_pos

/-- With the standard valuation assumptions, the same canonical transport gives
`r <= depthValue ell p d`. -/
theorem le_depthValue_of_baseHasHenselLift_canonical
    {ell omega g p d j r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hbase : BaseHasHenselLift ell g p d j r)
    (hcanon : HenselLiftCanonicalRep omega g p d j r)
    (hell_pos : 0 < ell) :
    r ≤ depthValue ell p d :=
  le_depthValue_of_depthAtLeast hN
    (depthAtLeast_of_baseHasHenselLift_canonical_of_base_pos hbase hcanon hell_pos)

end ApparitionDepth
