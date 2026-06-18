import ABD.ABD2.Reduction.CImageRealization

namespace ABD2
namespace ABCTriple

/-- The C-side tangent module, kept as an abbreviation so the bridge remains
visibly tied to the C support block. -/
abbrev CSupportTangent (T : ABCTriple) : Type :=
  Tangent T.supportC

/-- Extend a C-support tangent to the full tangent module by zero outside `S_c`. -/
def extendC (T : ABCTriple) (xC : T.CSupportTangent) : T.FullTangent :=
  fun p => if hp : p.1 ∈ T.supportC then xC ⟨p.1, hp⟩ else 0

/-- Restrict a full tangent to the C support block. -/
def restrictC (T : ABCTriple) (x : T.FullTangent) : T.CSupportTangent :=
  fun p =>
    x ⟨p.1, by
      unfold ABCTriple.support
      simp [p.2]⟩

/-- Restricting an extended C-tangent recovers the original C-tangent. -/
theorem restrictC_extendC
    (T : ABCTriple) (xC : T.CSupportTangent) :
    T.restrictC (T.extendC xC) = xC := by
  funext p
  simp [restrictC, extendC, p.2]

/-- The C-mask fixes an extended C-tangent. -/
theorem maskC_extendC_eq_extendC
    (T : ABCTriple) (xC : T.CSupportTangent) :
    T.maskC (T.extendC xC) = T.extendC xC := by
  funext p
  by_cases hpC : p.1 ∈ T.supportC
  · simp [ABCTriple.maskC, supportMask, extendC, hpC]
  · simp [ABCTriple.maskC, supportMask, extendC, hpC]

/-- An extended C-tangent is C-pure under a genuine A/B/C block decomposition. -/
theorem extendC_isCPure
    (T : ABCTriple) (h : T.SupportBlocksDecompose) (xC : T.CSupportTangent) :
    T.IsCPure (T.extendC xC) := by
  constructor
  · funext p
    by_cases hA : p.1 ∈ T.supportA
    · have hnotC : p.1 ∉ T.supportC := by
        intro hC
        exact Finset.disjoint_left.mp h.disjAC hA hC
      simp [ABCTriple.maskA, supportMask, extendC, hA, hnotC]
    · simp [ABCTriple.maskA, supportMask, hA]
  · funext p
    by_cases hB : p.1 ∈ T.supportB
    · have hnotC : p.1 ∉ T.supportC := by
        intro hC
        exact Finset.disjoint_left.mp h.disjBC hB hC
      simp [ABCTriple.maskB, supportMask, extendC, hB, hnotC]
    · simp [ABCTriple.maskB, supportMask, hB]

/-- A C-pure full tangent is recovered from its C restriction. -/
theorem extendC_restrictC_eq_of_isCPure
    (T : ABCTriple) (h : T.SupportBlocksDecompose)
    {x : T.FullTangent} (hpure : T.IsCPure x) :
    T.extendC (T.restrictC x) = x := by
  funext p
  by_cases hC : p.1 ∈ T.supportC
  · simp [extendC, restrictC, hC]
  · have hcover : p.1 ∈ T.supportA ∪ T.supportB ∪ T.supportC := by
      simp [h.cover]
    have hAB : p.1 ∈ T.supportA ∨ p.1 ∈ T.supportB := by
      simpa [hC] using hcover
    have hxzero : x p = 0 := by
      rcases hAB with hA | hB
      · have hmask := congrFun hpure.1 p
        simpa [ABCTriple.maskA, supportMask, hA] using hmask
      · have hmask := congrFun hpure.2 p
        simpa [ABCTriple.maskB, supportMask, hB] using hmask
    simp [extendC, hC, hxzero]

/-- C-support image: values obtained from C-support tangents after zero-extension. -/
def CSupportImage (T : ABCTriple) : Set ℤ :=
  {target | ∃ xC : T.CSupportTangent, T.cLinearForm (T.extendC xC) = target}

@[simp]
theorem mem_CSupportImage_iff
    (T : ABCTriple) (target : ℤ) :
    target ∈ T.CSupportImage ↔
      ∃ xC : T.CSupportTangent, T.cLinearForm (T.extendC xC) = target := by
  rfl

/-- Every C-support value is a C-image value. -/
theorem CSupportImage_subset_CImage
    (T : ABCTriple) (h : T.SupportBlocksDecompose) :
    T.CSupportImage ⊆ T.CImage := by
  intro target htarget
  rcases (T.mem_CSupportImage_iff target).1 htarget with ⟨xC, hxC⟩
  refine (T.mem_CImage_iff target).2 ?_
  exact ⟨T.extendC xC, T.extendC_isCPure h xC, hxC⟩

/-- Every C-image value is represented by a C-support tangent. -/
theorem CImage_subset_CSupportImage
    (T : ABCTriple) (h : T.SupportBlocksDecompose) :
    T.CImage ⊆ T.CSupportImage := by
  intro target htarget
  rcases (T.mem_CImage_iff target).1 htarget with ⟨x, hpure, hvalue⟩
  refine (T.mem_CSupportImage_iff target).2 ?_
  refine ⟨T.restrictC x, ?_⟩
  rw [T.extendC_restrictC_eq_of_isCPure h hpure]
  exact hvalue

/-- The C-image equals the image obtained from C-support tangents. -/
theorem CImage_eq_CSupportImage
    (T : ABCTriple) (h : T.SupportBlocksDecompose) :
    T.CImage = T.CSupportImage := by
  ext target
  constructor
  · intro htarget
    exact T.CImage_subset_CSupportImage h htarget
  · intro htarget
    exact T.CSupportImage_subset_CImage h htarget

end ABCTriple
end ABD2
