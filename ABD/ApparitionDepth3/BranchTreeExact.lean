/-
  ABD.ApparitionDepth3.BranchTreeExact

  Stage 12:
    * the p children above a finite Teichmuller representative;
    * exactly one child continues to level r+1;
    * every other child has exact depth r.
-/

import ABD.ApparitionDepth3.WittCarryBridge

namespace ApparitionDepth3

/-- The child selected by a residue digit above a representative at level r. -/
def branchChild
    {p : Nat} (omega : Nat) (t : ZMod p) (r : Nat) : Nat :=
  correctedRepresentative omega t.val p r

/-- A branch child reduces to its parent at the old precision. -/
theorem branchChild_reduce
    {omega p r : Nat} (t : ZMod p) :
    (branchChild omega t r : ZMod (p ^ r)) =
      (omega : ZMod (p ^ r)) := by
  unfold branchChild
  exact correctedRepresentative_reduce omega t.val p r

/-- Every child of a root at level r remains a root at level r. -/
theorem branchChild_rootAtLevel
    {omega p d r : Nat}
    (hroot : RootAtLevel omega p d r)
    (t : ZMod p) :
    RootAtLevel (branchChild omega t r) p d r := by
  unfold RootAtLevel at hroot ⊢
  rw [branchChild_reduce]
  exact hroot

/-- For the canonical p-adic branch, a child continues exactly when its digit
is the actual next ordinary p-adic digit. -/
theorem branchChild_rootAtNextLevel_iff
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (t : ZMod p) :
    RootAtLevel
        (branchChild (branchPadicRepresentative g p d j r) t r)
        p d (r + 1) ↔
      t = branchPadicDigit g p d j r := by
  let seed := branchSeed g p d j
  let omega := branchPadicRepresentative g p d j r
  have hsimple : SimpleRootModP seed p d := by
    simpa only [seed] using branchSeed_simpleRoot hcopG hprimitive hparams
  have hlift : LiftAtLevel seed omega p d r := by
    simpa only [seed, omega, TeichmullerLiftAtLevel] using
      (branchPadicRepresentative_teichmullerLift
        hcopG hprimitive hparams hrPos)
  have hiff := rootAtNextLevel_iff_digit_eq_canonical
    (seed := seed) (omega := omega) (t := t.val)
    hsimple hrPos hlift
  rw [branchPadicDigit_eq_henselCorrection
    hcopG hprimitive hparams hrPos]
  simpa only [branchChild, ZMod.natCast_zmod_val] using hiff

/-- The continuing child is unique as a residue digit. -/
theorem existsUnique_continuingBranchChild
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    ∃! t : ZMod p,
      RootAtLevel
        (branchChild (branchPadicRepresentative g p d j r) t r)
        p d (r + 1) := by
  refine ⟨branchPadicDigit g p d j r, ?_, ?_⟩
  · exact (branchChild_rootAtNextLevel_iff
      hcopG hprimitive hparams hrPos _).2 rfl
  · intro t ht
    exact (branchChild_rootAtNextLevel_iff
      hcopG hprimitive hparams hrPos t).1 ht

/-- Every child is positive because its canonical parent is positive. -/
theorem branchChild_pos
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (t : ZMod p) :
    0 < branchChild (branchPadicRepresentative g p d j r) t r := by
  have hlift := branchPadicRepresentative_teichmullerLift
    hcopG hprimitive hparams hrPos
  have hparent : 0 < branchPadicRepresentative g p d j r :=
    liftRepresentative_pos_of_simpleRoot
      (branchSeed_simpleRoot hcopG hprimitive hparams) hlift
  unfold branchChild correctedRepresentative
  exact lt_of_lt_of_le hparent (Nat.le_add_right _ _)

/-- A non-continuing child has exact root level r. -/
theorem branchChild_exactRootAtLevel_iff
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (t : ZMod p) :
    ExactRootAtLevel
        (branchChild (branchPadicRepresentative g p d j r) t r)
        p d r ↔
      t ≠ branchPadicDigit g p d j r := by
  unfold ExactRootAtLevel
  have hparentRoot :
      RootAtLevel (branchPadicRepresentative g p d j r) p d r :=
    branchPadicRepresentative_rootAtLevel hcopG hprimitive hparams
  have hchildRoot := branchChild_rootAtLevel hparentRoot t
  rw [branchChild_rootAtNextLevel_iff
    hcopG hprimitive hparams hrPos t]
  simp only [hchildRoot, true_and]

/-- A non-continuing child has exact arithmetic depth r. -/
theorem branchChild_exactDepth_iff
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (t : ZMod p) :
    ExactDepth
        (branchChild (branchPadicRepresentative g p d j r) t r)
        p d r ↔
      t ≠ branchPadicDigit g p d j r := by
  rw [← exactRootAtLevel_iff_exactDepth_of_base_pos
    (branchChild_pos hcopG hprimitive hparams hrPos t)]
  exact branchChild_exactRootAtLevel_iff
    hcopG hprimitive hparams hrPos t

/-- Every child remains in the same exact-order branch modulo p. -/
theorem branchChild_firstAppearsAt
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (t : ZMod p) :
    FirstAppearsAt
      (branchChild (branchPadicRepresentative g p d j r) t r) p d := by
  have hlift := branchPadicRepresentative_teichmullerLift
    hcopG hprimitive hparams hrPos
  have hsame :
      (branchChild (branchPadicRepresentative g p d j r) t r :
          ZMod (p ^ r)) =
        (branchPadicRepresentative g p d j r : ZMod (p ^ r)) :=
    branchChild_reduce t
  have hpos := branchChild_pos hcopG hprimitive hparams hrPos t
  exact (teichmullerClassResult
    hcopG hprimitive hparams hrPos hlift hsame hpos).firstWithDepth.1

/-- The p-1 non-continuing children are precisely the bases whose first
apparition is d and whose initial depth is exactly r. -/
theorem branchChild_firstAppearsWithExactDepth
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    {t : ZMod p}
    (ht : t ≠ branchPadicDigit g p d j r) :
    FirstAppearsWithExactDepth
      (branchChild (branchPadicRepresentative g p d j r) t r)
      p d r := by
  exact ⟨
    branchChild_firstAppearsAt hcopG hprimitive hparams hrPos t,
    (branchChild_exactDepth_iff
      hcopG hprimitive hparams hrPos t).2 ht⟩

/-- Public stage-12 package for the complete one-level branch law. -/
structure BranchTreeLevelResult
    (g p d j r : Nat) [Fact p.Prime] where
  continuingDigit : ZMod p
  continuing_eq : continuingDigit = branchPadicDigit g p d j r
  continues :
    RootAtLevel
      (branchChild (branchPadicRepresentative g p d j r)
        continuingDigit r) p d (r + 1)
  unique : ∀ t : ZMod p,
    RootAtLevel
      (branchChild (branchPadicRepresentative g p d j r) t r)
      p d (r + 1) → t = continuingDigit
  otherExact : ∀ t : ZMod p, t ≠ continuingDigit →
    FirstAppearsWithExactDepth
      (branchChild (branchPadicRepresentative g p d j r) t r)
      p d r

/-- Concrete construction of the complete one-level branch law. -/
noncomputable def branchTreeLevelResult
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    BranchTreeLevelResult g p d j r := by
  refine
    { continuingDigit := branchPadicDigit g p d j r
      continuing_eq := rfl
      continues := (branchChild_rootAtNextLevel_iff
        hcopG hprimitive hparams hrPos _).2 rfl
      unique := ?_
      otherExact := ?_ }
  · intro t ht
    exact (branchChild_rootAtNextLevel_iff
      hcopG hprimitive hparams hrPos t).1 ht
  · intro t ht
    exact branchChild_firstAppearsWithExactDepth
      hcopG hprimitive hparams hrPos ht

end ApparitionDepth3
