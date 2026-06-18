import ABD.ABD.PastenBlock.DerivativeRestriction

namespace ABD

/--
Support-level primitive condition for the block normal form.

This is the exact condition needed to treat the full Pasten support as three
non-overlapping blocks `S_a`, `S_b`, and `S_c`.  A later arithmetic lemma can
connect the usual condition `Nat.Coprime T.a T.b` to this support-level form.
-/
structure ABCTriple.SupportBlocksDisjoint (T : ABCTriple) : Prop where
  disjointAB : ∀ {p : ℕ}, p ∈ T.supportA → p ∈ T.supportB → False
  disjointAC : ∀ {p : ℕ}, p ∈ T.supportA → p ∈ T.supportC → False
  disjointBC : ∀ {p : ℕ}, p ∈ T.supportB → p ∈ T.supportC → False

/-- Alias for the support-level primitive hypothesis used by the block normal
form. -/
abbrev ABCTriple.PrimitiveSupport (T : ABCTriple) : Prop :=
  T.SupportBlocksDisjoint

/-- The three independent tangent blocks attached to `S_a`, `S_b`, and `S_c`. -/
@[ext]
structure ABCTriple.TangentBlocks (T : ABCTriple) where
  xA : T.ATangent
  xB : T.BTangent
  xC : T.CTangent

/-- Restrict a full tangent vector to its three support blocks. -/
def ABCTriple.toBlocks (T : ABCTriple) (x : Tangent T.support) : T.TangentBlocks where
  xA := T.restrictA x
  xB := T.restrictB x
  xC := T.restrictC x

/-- Glue three block tangents into a full tangent vector on the Pasten support.

The definition gives priority to the `a` block and then the `b` block.  Under
`SupportBlocksDisjoint`, this priority is irrelevant, and the restriction
lemmas below recover the original blocks. -/
def ABCTriple.glueBlocks (T : ABCTriple) (x : T.TangentBlocks) : Tangent T.support :=
  fun hp =>
    if hA : hp.1 ∈ T.supportA then
      x.xA ⟨hp.1, hA⟩
    else if hB : hp.1 ∈ T.supportB then
      x.xB ⟨hp.1, hB⟩
    else
      x.xC ⟨hp.1, by
        have hmem : hp.1 ∈ T.support := hp.2
        unfold ABCTriple.support at hmem
        simp only [Finset.mem_union] at hmem
        rcases hmem with hmemA | hmemBC
        · exact False.elim (hA (by simpa [ABCTriple.supportA] using hmemA))
        · rcases hmemBC with hmemB | hmemC
          · exact False.elim (hB (by simpa [ABCTriple.supportB] using hmemB))
          · simpa [ABCTriple.supportC] using hmemC⟩

@[simp]
theorem ABCTriple.restrictA_glueBlocks
    (T : ABCTriple) (x : T.TangentBlocks) :
    T.restrictA (T.glueBlocks x) = x.xA := by
  funext hp
  unfold ABCTriple.restrictA ABCTriple.glueBlocks
  simp [hp.2]

@[simp]
theorem ABCTriple.restrictB_glueBlocks
    (T : ABCTriple) (hdisj : T.SupportBlocksDisjoint) (x : T.TangentBlocks) :
    T.restrictB (T.glueBlocks x) = x.xB := by
  funext hp
  have hnotA : hp.1 ∉ T.supportA := by
    intro hA
    exact hdisj.disjointAB hA hp.2
  unfold ABCTriple.restrictB ABCTriple.glueBlocks
  simp [hnotA, hp.2]

@[simp]
theorem ABCTriple.restrictC_glueBlocks
    (T : ABCTriple) (hdisj : T.SupportBlocksDisjoint) (x : T.TangentBlocks) :
    T.restrictC (T.glueBlocks x) = x.xC := by
  funext hp
  have hnotA : hp.1 ∉ T.supportA := by
    intro hA
    exact hdisj.disjointAC hA hp.2
  have hnotB : hp.1 ∉ T.supportB := by
    intro hB
    exact hdisj.disjointBC hB hp.2
  unfold ABCTriple.restrictC ABCTriple.glueBlocks
  simp [hnotA, hnotB]

/-- The block-balance equation attached to the three separated support blocks. -/
def ABCTriple.BlockBalance (T : ABCTriple) (x : T.TangentBlocks) : Prop :=
  formalDeriv T.supportA x.xA T.a +
      formalDeriv T.supportB x.xB T.b =
    formalDeriv T.supportC x.xC T.c

/-- The already-existing Pasten additive condition is exactly block balance for
the block decomposition of a full tangent vector. -/
theorem ABCTriple.mem_pastenT_iff_blockBalance_toBlocks
    (T : ABCTriple) (x : Tangent T.support) :
    x ∈ PastenT T ↔ T.BlockBalance (T.toBlocks x) := by
  unfold ABCTriple.BlockBalance ABCTriple.toBlocks
  exact T.mem_pastenT_iff_restrict_block_equation x

/-- Under the support-level primitive hypothesis, gluing blocks and then asking
for membership in `PastenT` is exactly the block-balance equation. -/
theorem ABCTriple.glueBlocks_mem_pastenT_iff_blockBalance
    (T : ABCTriple) (hdisj : T.SupportBlocksDisjoint) (x : T.TangentBlocks) :
    T.glueBlocks x ∈ PastenT T ↔ T.BlockBalance x := by
  rw [T.mem_pastenT_iff_restrict_block_equation]
  unfold ABCTriple.BlockBalance
  rw [T.restrictA_glueBlocks]
  rw [T.restrictB_glueBlocks hdisj]
  rw [T.restrictC_glueBlocks hdisj]

end ABD
