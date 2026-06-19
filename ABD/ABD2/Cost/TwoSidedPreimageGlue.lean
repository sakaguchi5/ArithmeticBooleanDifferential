import ABD.ABD2.Cost.TwoSidedPreimage

namespace ABD2
namespace ABCTriple

/-- A-mask of an A/B glued tangent recovers the original A-mask.

This is the Boolean direct-sum fact needed by D1: if the A and B support blocks
are disjoint, then adding a B-masked vector does not change the A-mask. -/
theorem maskA_maskA_add_maskB_eq_maskA
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (xA xB : T.FullTangent) :
    T.maskA (T.maskA xA + T.maskB xB) = T.maskA xA := by
  funext p
  by_cases hpA : p.1 ∈ T.supportA
  · have hpB : p.1 ∉ T.supportB := by
      intro hpB
      exact Finset.disjoint_left.mp hblocks.disjAB hpA hpB
    simp [ABCTriple.maskA, ABCTriple.maskB, supportMask, hpA, hpB]
  · simp [ABCTriple.maskA, supportMask, hpA]

/-- B-mask of an A/B glued tangent recovers the original B-mask.

This is the symmetric Boolean direct-sum fact needed by D1. -/
theorem maskB_maskA_add_maskB_eq_maskB
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (xA xB : T.FullTangent) :
    T.maskB (T.maskA xA + T.maskB xB) = T.maskB xB := by
  funext p
  by_cases hpB : p.1 ∈ T.supportB
  · have hpA : p.1 ∉ T.supportA := by
      intro hpA
      exact Finset.disjoint_left.mp hblocks.disjAB hpA hpB
    simp [ABCTriple.maskA, ABCTriple.maskB, supportMask, hpA, hpB]
  · simp [ABCTriple.maskB, supportMask, hpB]

/-- The A-derivative value of an A/B glued tangent is the A-derivative value of
its A witness. -/
theorem ADerivValue_maskA_add_maskB_eq_left
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (xA xB : T.FullTangent) :
    T.ADerivValue (T.maskA xA + T.maskB xB) = T.ADerivValue xA := by
  unfold ABCTriple.ADerivValue
  calc
    formalDeriv T.support (T.maskA xA + T.maskB xB) T.a
        = formalDeriv T.support (T.maskA (T.maskA xA + T.maskB xB)) T.a := by
            exact (T.formalDeriv_a_eq_maskA (T.maskA xA + T.maskB xB)).symm
    _ = formalDeriv T.support (T.maskA xA) T.a := by
            rw [T.maskA_maskA_add_maskB_eq_maskA hblocks xA xB]
    _ = formalDeriv T.support xA T.a := by
            exact T.formalDeriv_a_eq_maskA xA

/-- The B-derivative value of an A/B glued tangent is the B-derivative value of
its B witness. -/
theorem BDerivValue_maskA_add_maskB_eq_right
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (xA xB : T.FullTangent) :
    T.BDerivValue (T.maskA xA + T.maskB xB) = T.BDerivValue xB := by
  unfold ABCTriple.BDerivValue
  calc
    formalDeriv T.support (T.maskA xA + T.maskB xB) T.b
        = formalDeriv T.support (T.maskB (T.maskA xA + T.maskB xB)) T.b := by
            exact (T.formalDeriv_b_eq_maskB (T.maskA xA + T.maskB xB)).symm
    _ = formalDeriv T.support (T.maskB xB) T.b := by
            rw [T.maskB_maskA_add_maskB_eq_maskB hblocks xA xB]
    _ = formalDeriv T.support xB T.b := by
            exact T.formalDeriv_b_eq_maskB xB

/-- Boolean mask/direct-sum proves the D1 A/B preimage glue principle.

Separately realizing `t` on the A side and `-t` on the B side can be combined by
`maskA xA + maskB xB`.  The two component bounds are preserved because the
corresponding masks of the glued tangent are definitionally the original masks. -/
theorem twoSidedPreimageGlue_of_supportBlocksDecompose
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose) :
    T.TwoSidedPreimageGlue := by
  intro t BA BB hA hB
  rcases T.exists_witness_of_aPreimageCostAtMost hA with ⟨xA, hAval, hsmallA⟩
  rcases T.exists_witness_of_bPreimageCostAtMost hB with ⟨xB, hBval, hsmallB⟩
  let x : T.FullTangent := T.maskA xA + T.maskB xB
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · calc
      T.ADerivValue x = T.ADerivValue xA := by
        simpa [x] using T.ADerivValue_maskA_add_maskB_eq_left hblocks xA xB
      _ = t := hAval
  · calc
      T.BDerivValue x = T.BDerivValue xB := by
        simpa [x] using T.BDerivValue_maskA_add_maskB_eq_right hblocks xA xB
      _ = -t := hBval
  · have hmask : T.maskA x = T.maskA xA := by
      simpa [x] using T.maskA_maskA_add_maskB_eq_maskA hblocks xA xB
    change T.SmallTangent (T.maskA x) BA
    rw [hmask]
    simpa [ABCTriple.APreimageSmall] using hsmallA
  · have hmask : T.maskB x = T.maskB xB := by
      simpa [x] using T.maskB_maskA_add_maskB_eq_maskB hblocks xA xB
    change T.SmallTangent (T.maskB x) BB
    rw [hmask]
    simpa [ABCTriple.BPreimageSmall] using hsmallB

end ABCTriple
end ABD2
