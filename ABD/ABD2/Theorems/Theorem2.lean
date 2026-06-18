import ABD.ABD2.Pasten.Wronskian

namespace ABD2
namespace ABCTriple

/-- Theorem 2, ABD2 surface form: the Wronskian only depends on the A/B masks. -/
theorem Theorem2_wronskian_eq_AB_masks
    (T : ABCTriple) (x : T.FullTangent) :
    T.Wronskian x =
      (T.a : ℤ) * formalDeriv T.support (T.maskB x) T.b -
        (T.b : ℤ) * formalDeriv T.support (T.maskA x) T.a := by
  exact T.Wronskian_eq_AB_masks x

/-- If two tangents have the same A/B masks, they have the same Wronskian. -/
theorem Theorem2_wronskian_congr_AB_masks
    (T : ABCTriple) (x y : T.FullTangent)
    (hA : T.maskA x = T.maskA y)
    (hB : T.maskB x = T.maskB y) :
    T.Wronskian x = T.Wronskian y := by
  exact T.Wronskian_congr_AB_masks x y hA hB

/-- Nondegeneracy is also invariant under preserving the A/B masks. -/
theorem Theorem2_nondegenerate_congr_AB_masks
    (T : ABCTriple) (x y : T.FullTangent)
    (hA : T.maskA x = T.maskA y)
    (hB : T.maskB x = T.maskB y) :
    T.Nondegenerate x ↔ T.Nondegenerate y := by
  unfold ABCTriple.Nondegenerate
  rw [T.Wronskian_congr_AB_masks x y hA hB]

/-- Under an A/B/C support decomposition, the C mask is invisible to the Wronskian
once the A/B masks are fixed. -/
theorem Theorem2_wronskian_ignores_C_mask
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose) (x : T.FullTangent) :
    T.Wronskian (T.maskA x + T.maskB x + T.maskC x) =
      T.Wronskian (T.maskA x + T.maskB x) := by
  exact T.Wronskian_ignores_C_mask hblocks x

end ABCTriple
end ABD2
