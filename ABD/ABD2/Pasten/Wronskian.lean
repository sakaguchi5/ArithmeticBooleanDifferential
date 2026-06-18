import ABD.ABD2.Pasten.PastenT

namespace ABD2
namespace ABCTriple

/-- Pasten Wronskian. -/
def Wronskian (T : ABCTriple) (x : T.FullTangent) : ℤ :=
  (T.a : ℤ) * formalDeriv T.support x T.b -
    (T.b : ℤ) * formalDeriv T.support x T.a

/-- Wronskian nondegeneracy. -/
def Nondegenerate (T : ABCTriple) (x : T.FullTangent) : Prop :=
  T.Wronskian x ≠ 0

/-- The Wronskian only sees the A/B Boolean masks. -/
theorem Wronskian_eq_AB_masks
    (T : ABCTriple) (x : T.FullTangent) :
    T.Wronskian x =
      (T.a : ℤ) * formalDeriv T.support (T.maskB x) T.b -
        (T.b : ℤ) * formalDeriv T.support (T.maskA x) T.a := by
  unfold Wronskian
  rw [T.formalDeriv_b_eq_maskB x]
  rw [T.formalDeriv_a_eq_maskA x]

/-- If two tangents have the same A and B masks, they have the same Wronskian. -/
theorem Wronskian_congr_AB_masks
    (T : ABCTriple) (x y : T.FullTangent)
    (hA : T.maskA x = T.maskA y)
    (hB : T.maskB x = T.maskB y) :
    T.Wronskian x = T.Wronskian y := by
  rw [T.Wronskian_eq_AB_masks x]
  rw [T.Wronskian_eq_AB_masks y]
  simpa [ABCTriple.maskA, ABCTriple.maskB] using
    congrArg₂
      (fun u v =>
        (T.a : ℤ) * formalDeriv T.support v T.b -
          (T.b : ℤ) * formalDeriv T.support u T.a)
      hA hB

/-- Under an orthogonal A/B/C support decomposition, the C mask is invisible to
the Wronskian after the A/B masks are fixed. -/
theorem Wronskian_ignores_C_mask
    (T : ABCTriple) (h : T.SupportBlocksDecompose) (x : T.FullTangent) :
    T.Wronskian (T.maskA x + T.maskB x + T.maskC x) =
      T.Wronskian (T.maskA x + T.maskB x) := by
  apply T.Wronskian_congr_AB_masks
  · funext p
    by_cases hA : p.1 ∈ T.supportA
    · have hB : p.1 ∉ T.supportB := by
        intro hb
        exact Finset.disjoint_left.mp h.disjAB hA hb
      have hC : p.1 ∉ T.supportC := by
        intro hc
        exact Finset.disjoint_left.mp h.disjAC hA hc
      simp [ABCTriple.maskA, ABCTriple.maskB, ABCTriple.maskC, supportMask, hA, hB, hC]
    · simp [ABCTriple.maskA, supportMask, hA]
  · funext p
    by_cases hB : p.1 ∈ T.supportB
    · have hA : p.1 ∉ T.supportA := by
        intro ha
        exact Finset.disjoint_left.mp h.disjAB ha hB
      have hC : p.1 ∉ T.supportC := by
        intro hc
        exact Finset.disjoint_left.mp h.disjBC hB hc
      simp [ABCTriple.maskA, ABCTriple.maskB, ABCTriple.maskC, supportMask, hA, hB, hC]
    · simp [ABCTriple.maskB, supportMask, hB]

end ABCTriple
end ABD2
