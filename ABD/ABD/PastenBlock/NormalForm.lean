import ABD.ABD.PastenBlock.Wronskian

namespace ABD

/--
A block-normal presentation of a strict Pasten candidate.

This is intentionally placed in `ABD/PastenBlock`, not in `ABD/Lattice`: it is a
coordinate-level normal form for Pasten's original data, not a new lattice
existence theorem.  The additive condition is written as the three block values
`D(a), D(b), D(c)`, and nondegeneracy is written as the `a/b` block Wronskian.
-/
structure StrictBlockCandidate (T : ABCTriple) where
  x : Tangent T.support
  block_equation : T.derivA x + T.derivB x = T.derivC x
  block_wronskian_ne_zero : T.blockWronskian x ≠ 0

/-- The block-normal candidate is the same data as a strict Pasten candidate. -/
def StrictBlockCandidate.toStrictPastenCandidate
    {T : ABCTriple} (h : StrictBlockCandidate T) : StrictPastenCandidate T where
  x := h.x
  mem_T := (T.mem_pastenT_iff_block_equation h.x).2 h.block_equation
  nondegenerate :=
    (T.pastenNondegenerate_iff_blockWronskian_ne_zero h.x).2
      h.block_wronskian_ne_zero

/-- A strict Pasten candidate has a block-normal presentation. -/
def StrictPastenCandidate.toStrictBlockCandidate
    {T : ABCTriple} (h : StrictPastenCandidate T) : StrictBlockCandidate T where
  x := h.x
  block_equation := (T.mem_pastenT_iff_block_equation h.x).1 h.mem_T
  block_wronskian_ne_zero :=
    (T.pastenNondegenerate_iff_blockWronskian_ne_zero h.x).1 h.nondegenerate

@[simp]
theorem StrictBlockCandidate.toStrictPastenCandidate_x
    {T : ABCTriple} (h : StrictBlockCandidate T) :
    h.toStrictPastenCandidate.x = h.x := rfl

@[simp]
theorem StrictPastenCandidate.toStrictBlockCandidate_x
    {T : ABCTriple} (h : StrictPastenCandidate T) :
    h.toStrictBlockCandidate.x = h.x := rfl

/-- Existence of a strict Pasten candidate is equivalent to existence of its
block-normal presentation. -/
theorem hasStrictPastenCandidate_iff_nonempty_strictBlockCandidate
    (T : ABCTriple) :
    HasStrictPastenCandidate T ↔ Nonempty (StrictBlockCandidate T) := by
  constructor
  · intro h
    rcases h with ⟨x, hT, hnd⟩
    exact ⟨
      { x := x
        block_equation := (T.mem_pastenT_iff_block_equation x).1 hT
        block_wronskian_ne_zero :=
          (T.pastenNondegenerate_iff_blockWronskian_ne_zero x).1 hnd }⟩
  · intro h
    rcases h with ⟨h⟩
    exact h.toStrictPastenCandidate.hasStrictPastenCandidate

end ABD
