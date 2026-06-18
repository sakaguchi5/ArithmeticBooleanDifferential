import ABD.ABD2.Reduction.StrictFromProfile

namespace ABD2
namespace ABCTriple

/-- Orthogonality: A after C is zero. -/
theorem maskA_maskC_eq_zero
    (T : ABCTriple) (h : T.SupportBlocksDecompose) (x : T.FullTangent) :
    T.maskA (T.maskC x) = 0 := by
  simpa [ABCTriple.maskA, ABCTriple.maskC] using
    (supportMask_comp_eq_zero_of_disjoint
      T.support T.supportA T.supportC h.disjAC x)

/-- Orthogonality: B after C is zero. -/
theorem maskB_maskC_eq_zero
    (T : ABCTriple) (h : T.SupportBlocksDecompose) (x : T.FullTangent) :
    T.maskB (T.maskC x) = 0 := by
  simpa [ABCTriple.maskB, ABCTriple.maskC] using
    (supportMask_comp_eq_zero_of_disjoint
      T.support T.supportB T.supportC h.disjBC x)

/-- The C-mask of any tangent is C-pure under an A/B/C block decomposition. -/
theorem isCPure_maskC
    (T : ABCTriple) (h : T.SupportBlocksDecompose) (x : T.FullTangent) :
    T.IsCPure (T.maskC x) := by
  constructor
  · exact T.maskA_maskC_eq_zero h x
  · exact T.maskB_maskC_eq_zero h x

/-- The C-linear form is unchanged by first applying the C-mask. -/
theorem cLinearForm_maskC_eq_self
    (T : ABCTriple) (x : T.FullTangent) :
    T.cLinearForm (T.maskC x) = T.cLinearForm x := by
  unfold ABCTriple.cLinearForm
  rw [T.maskC_idempotent x]

/-- Membership in `PastenT` says exactly that the AB target is absorbed by the
C-linear form. -/
theorem abTarget_eq_cLinearForm_of_mem_PastenT
    (T : ABCTriple) {x : T.FullTangent} (hx : x ∈ T.PastenT) :
    T.abTarget x = T.cLinearForm x := by
  have hbalance := (T.mem_PastenT_iff_blockBalance x).1 hx
  simpa [ABCTriple.BlockBalance, ABCTriple.abTarget, ABCTriple.cLinearForm]
    using hbalance

/-- A Pasten tangent has its AB target in the C-image: the witness is its C-mask. -/
theorem abTarget_mem_CImage_of_mem_PastenT
    (T : ABCTriple) (h : T.SupportBlocksDecompose)
    {x : T.FullTangent} (hx : x ∈ T.PastenT) :
    T.abTarget x ∈ T.CImage := by
  refine (T.mem_CImage_iff (T.abTarget x)).2 ?_
  refine ⟨T.maskC x, T.isCPure_maskC h x, ?_⟩
  have htarget : T.abTarget x = T.cLinearForm x :=
    T.abTarget_eq_cLinearForm_of_mem_PastenT hx
  rw [T.cLinearForm_maskC_eq_self x]
  exact htarget.symm

/-- A strict candidate rules out the seed-level bad pattern, provided the chosen
profile really realizes the C-image.

This is the reverse direction missing from the earlier one-way routing theorem. -/
theorem not_BadSeed_of_hasStrictCandidate_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (hstrict : T.HasStrictCandidate) :
    ¬ T.BadSeed P := by
  rcases hstrict with ⟨x, hxstrict⟩
  rcases hxstrict with ⟨hxPasten, hxNondegenerate⟩
  have hmemImage : T.abTarget x ∈ T.CImage :=
    T.abTarget_mem_CImage_of_mem_PastenT hblocks hxPasten
  have hdiv : P.gcd ∣ T.abTarget x :=
    (hreal (T.abTarget x)).1 hmemImage
  have hxCompatible : x ∈ T.ABCompatibleSubmodule P :=
    (T.mem_ABCompatibleSubmodule_iff P x).2 hdiv
  have hxNotKernel : x ∉ T.ABWronskianKernel := by
    intro hxKernel
    exact hxNondegenerate ((T.mem_ABWronskianKernel_iff x).1 hxKernel)
  have hgood : T.HasGoodABSeed P :=
    ⟨x, hxCompatible, hxNotKernel⟩
  exact (T.hasGoodABSeed_iff_not_BadSeed P).1 hgood

/-- For a realized C-image profile, strict candidates are equivalent to failure
of the first bad-seed pattern.

This is the ABD2 profile-level analogue of the old Theorem 1--3 composite
strengthening. -/
theorem hasStrictCandidate_iff_not_BadSeed_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P) :
    T.HasStrictCandidate ↔ ¬ T.BadSeed P := by
  constructor
  · intro hstrict
    exact T.not_BadSeed_of_hasStrictCandidate_of_profileRealizesCImage
      P hblocks hreal hstrict
  · intro hgood
    exact T.hasStrictCandidate_of_not_BadSeed_of_profileRealizesCImage
      P hblocks hreal hgood

end ABCTriple
end ABD2
