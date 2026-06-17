import ABD.PastenBlock.PrimitiveAB

namespace ABD

/-- Gluing the block restrictions of a full tangent vector recovers the original
full tangent vector.  This direction does not need disjointness: even if supports
overlapped, all branches read the same original full coordinate. -/
theorem ABCTriple.glueBlocks_toBlocks
    (T : ABCTriple) (x : Tangent T.support) :
    T.glueBlocks (T.toBlocks x) = x := by
  funext hp
  unfold ABCTriple.glueBlocks ABCTriple.toBlocks
  unfold ABCTriple.restrictA ABCTriple.restrictB ABCTriple.restrictC
  by_cases hA : hp.1 ∈ T.supportA
  · simp [hA]
  · by_cases hB : hp.1 ∈ T.supportB
    · simp [hA, hB]
    · have hC : hp.1 ∈ T.supportC := by
        have hmem : hp.1 ∈ T.support := hp.2
        unfold ABCTriple.support at hmem
        simp only [Finset.mem_union] at hmem
        rcases hmem with hmemA | hmemBC
        · exact False.elim (hA (by simpa [ABCTriple.supportA] using hmemA))
        · rcases hmemBC with hmemB | hmemC
          · exact False.elim (hB (by simpa [ABCTriple.supportB] using hmemB))
          · simpa [ABCTriple.supportC] using hmemC
      simp [hA, hB]

/-- Under support-block disjointness, restricting glued blocks recovers exactly
those blocks. -/
theorem ABCTriple.toBlocks_glueBlocks
    (T : ABCTriple) (hdisj : T.SupportBlocksDisjoint) (x : T.TangentBlocks) :
    T.toBlocks (T.glueBlocks x) = x := by
  ext hp
  · exact congrFun (T.restrictA_glueBlocks x) hp
  · exact congrFun (T.restrictB_glueBlocks hdisj x) hp
  · exact congrFun (T.restrictC_glueBlocks hdisj x) hp

/-- The direct-sum equivalence between full tangents on `S_a ∪ S_b ∪ S_c` and
triple block tangents. -/
def ABCTriple.tangentBlocksEquiv
    (T : ABCTriple) (hdisj : T.SupportBlocksDisjoint) :
    Tangent T.support ≃ T.TangentBlocks where
  toFun := T.toBlocks
  invFun := T.glueBlocks
  left_inv := T.glueBlocks_toBlocks
  right_inv := T.toBlocks_glueBlocks hdisj

@[simp]
theorem ABCTriple.tangentBlocksEquiv_apply
    (T : ABCTriple) (hdisj : T.SupportBlocksDisjoint)
    (x : Tangent T.support) :
    T.tangentBlocksEquiv hdisj x = T.toBlocks x := by
  rfl

@[simp]
theorem ABCTriple.tangentBlocksEquiv_symm_apply
    (T : ABCTriple) (hdisj : T.SupportBlocksDisjoint)
    (x : T.TangentBlocks) :
    (T.tangentBlocksEquiv hdisj).symm x = T.glueBlocks x := by
  rfl

/-- Theorem 1 in direct-sum form: via the tangent-block equivalence, Pasten's
additive condition is exactly block balance. -/
theorem ABCTriple.pastenT_iff_blockBalance_under_directSum
    (T : ABCTriple) (hdisj : T.SupportBlocksDisjoint) (x : T.TangentBlocks) :
    (T.tangentBlocksEquiv hdisj).symm x ∈ PastenT T ↔ T.BlockBalance x := by
  simpa using T.glueBlocks_mem_pastenT_iff_blockBalance hdisj x

/-- Theorem 1 in the usual primitive form `gcd(a,b)=1`. -/
theorem ABCTriple.pastenT_iff_blockBalance_of_coprimeAB
    (T : ABCTriple) (hcop : Nat.Coprime T.a T.b) (x : T.TangentBlocks) :
    (T.tangentBlocksEquiv (T.supportBlocksDisjoint_of_coprimeAB hcop)).symm x
        ∈ PastenT T ↔
      T.BlockBalance x := by
  exact T.pastenT_iff_blockBalance_under_directSum
    (T.supportBlocksDisjoint_of_coprimeAB hcop) x

end ABD
