import ABD.ABD2.Reduction.CImageRealization
import ABD.ABD2.Reduction.CFiber

namespace ABD2
namespace ABCTriple

/-- A-mask idempotence in triple notation. -/
theorem maskA_idempotent
    (T : ABCTriple) (x : T.FullTangent) :
    T.maskA (T.maskA x) = T.maskA x := by
  simpa [ABCTriple.maskA] using
    (supportMask_idempotent T.support T.supportA x)

/-- B-mask idempotence in triple notation. -/
theorem maskB_idempotent
    (T : ABCTriple) (x : T.FullTangent) :
    T.maskB (T.maskB x) = T.maskB x := by
  simpa [ABCTriple.maskB] using
    (supportMask_idempotent T.support T.supportB x)

/-- C-mask idempotence in triple notation. -/
theorem maskC_idempotent
    (T : ABCTriple) (x : T.FullTangent) :
    T.maskC (T.maskC x) = T.maskC x := by
  simpa [ABCTriple.maskC] using
    (supportMask_idempotent T.support T.supportC x)

/-- Orthogonality: A after B is zero. -/
theorem maskA_maskB_eq_zero
    (T : ABCTriple) (h : T.SupportBlocksDecompose) (x : T.FullTangent) :
    T.maskA (T.maskB x) = 0 := by
  simpa [ABCTriple.maskA, ABCTriple.maskB] using
    (supportMask_comp_eq_zero_of_disjoint
      T.support T.supportA T.supportB h.disjAB x)

/-- Orthogonality: B after A is zero. -/
theorem maskB_maskA_eq_zero
    (T : ABCTriple) (h : T.SupportBlocksDecompose) (x : T.FullTangent) :
    T.maskB (T.maskA x) = 0 := by
  simpa [ABCTriple.maskA, ABCTriple.maskB] using
    (supportMask_comp_eq_zero_of_disjoint
      T.support T.supportB T.supportA h.disjAB.symm x)

/-- Orthogonality: C after A is zero. -/
theorem maskC_maskA_eq_zero
    (T : ABCTriple) (h : T.SupportBlocksDecompose) (x : T.FullTangent) :
    T.maskC (T.maskA x) = 0 := by
  simpa [ABCTriple.maskA, ABCTriple.maskC] using
    (supportMask_comp_eq_zero_of_disjoint
      T.support T.supportC T.supportA h.disjAC.symm x)

/-- Orthogonality: C after B is zero. -/
theorem maskC_maskB_eq_zero
    (T : ABCTriple) (h : T.SupportBlocksDecompose) (x : T.FullTangent) :
    T.maskC (T.maskB x) = 0 := by
  simpa [ABCTriple.maskB, ABCTriple.maskC] using
    (supportMask_comp_eq_zero_of_disjoint
      T.support T.supportC T.supportB h.disjBC.symm x)

/-- The C-linear form kills the A-masked part. -/
theorem cLinearForm_maskA_eq_zero
    (T : ABCTriple) (h : T.SupportBlocksDecompose) (x : T.FullTangent) :
    T.cLinearForm (T.maskA x) = 0 := by
  unfold ABCTriple.cLinearForm
  rw [T.maskC_maskA_eq_zero h x]
  simp

/-- The C-linear form kills the B-masked part. -/
theorem cLinearForm_maskB_eq_zero
    (T : ABCTriple) (h : T.SupportBlocksDecompose) (x : T.FullTangent) :
    T.cLinearForm (T.maskB x) = 0 := by
  unfold ABCTriple.cLinearForm
  rw [T.maskC_maskB_eq_zero h x]
  simp

/-- If a profile realizes the C-image, then every compatible seed admits a C-lift.

This is the abstract ABD2 replacement for the constructive part of the old
Theorem 3.  The actual arithmetic theorem should later prove that the concrete
`cCoeffGCDProfile` realizes the C-image. -/
theorem hasCLiftForCompatibleSeeds_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P) :
    T.HasCLiftForCompatibleSeeds P := by
  intro seed hseed
  have htarget : T.abTarget seed ∈ T.CImage :=
    T.abTarget_mem_CImage_of_mem_ABCompatibleSubmodule P seed hreal hseed
  rcases (T.mem_CImage_iff (T.abTarget seed)).1 htarget with
    ⟨cpart, hpure, hvalue⟩
  let lift : T.FullTangent := (T.maskA seed + T.maskB seed) + cpart
  refine ⟨lift, ?_⟩
  refine
    { maskA_eq := ?_
      maskB_eq := ?_
      c_balance := ?_ }
  · dsimp [lift]
    rw [T.maskA_add (T.maskA seed + T.maskB seed) cpart]
    rw [T.maskA_add (T.maskA seed) (T.maskB seed)]
    rw [T.maskA_idempotent seed]
    rw [T.maskA_maskB_eq_zero hblocks seed]
    rw [hpure.1]
    simp
  · dsimp [lift]
    rw [T.maskB_add (T.maskA seed + T.maskB seed) cpart]
    rw [T.maskB_add (T.maskA seed) (T.maskB seed)]
    rw [T.maskB_maskA_eq_zero hblocks seed]
    rw [T.maskB_idempotent seed]
    rw [hpure.2]
    simp
  · dsimp [lift]
    rw [T.cLinearForm_add (T.maskA seed + T.maskB seed) cpart]
    rw [T.cLinearForm_add (T.maskA seed) (T.maskB seed)]
    rw [T.cLinearForm_maskA_eq_zero hblocks seed]
    rw [T.cLinearForm_maskB_eq_zero hblocks seed]
    rw [hvalue]
    simp

end ABCTriple
end ABD2
