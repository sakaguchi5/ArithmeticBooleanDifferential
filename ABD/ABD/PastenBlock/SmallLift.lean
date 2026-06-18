import ABD.ABD.PastenBlock.StrictReduction

namespace ABD

/-- A block-level datum strong enough to build a small strict Pasten candidate.

This is deliberately not the final Small Derivatives Conjecture.  It separates
what Theorems 1--3 already know how to route from the genuinely hard task of
constructing a small lift. -/
structure ABCTriple.SmallBlockLiftData
    (T : ABCTriple) (B : ℤ) where
  xA : T.ATangent
  xB : T.BTangent
  xC : T.CTangent
  balance : T.cLinearForm xC = T.abSeedTarget xA xB
  nondegenerate : (xA, xB) ∉ T.ABWronskianHyperplaneSubmodule
  small :
    SmallTangent T.support
      (T.glueBlocks { xA := xA, xB := xB, xC := xC })
      B

/-- The routing part of the future Theorem 4: once a small block lift datum is
provided, Theorems 1--3 turn it into a small strict Pasten candidate. -/
theorem ABCTriple.hasSmallStrictPastenCandidate_of_smallBlockLiftData
    (T : ABCTriple) (hcop : Nat.Coprime T.a T.b) {B : ℤ}
    (h : T.SmallBlockLiftData B) :
    HasSmallStrictPastenCandidate T B := by
  let blocks : T.TangentBlocks :=
    { xA := h.xA
      xB := h.xB
      xC := h.xC }
  have hdisj : T.SupportBlocksDisjoint :=
    T.supportBlocksDisjoint_of_coprimeAB hcop
  have hbalance : T.BlockBalance blocks := by
    unfold ABCTriple.BlockBalance
    have hbal := h.balance
    unfold ABCTriple.cLinearForm ABCTriple.abSeedTarget at hbal
    simpa [blocks] using hbal.symm
  have hmem : T.glueBlocks blocks ∈ PastenT T :=
    (T.glueBlocks_mem_pastenT_iff_blockBalance hdisj blocks).2 hbalance
  have hnd : T.PastenNondegenerate (T.glueBlocks blocks) :=
    (T.glueBlocks_pastenNondegenerate_iff_ab_not_mem_hyperplaneSubmodule
      hdisj blocks).2 (by simpa [blocks] using h.nondegenerate)
  refine ⟨T.glueBlocks blocks, hmem, hnd, ?_⟩
  simpa [blocks] using h.small

end ABD
