import ABD.ABD2.Reduction.SmallLiftData

namespace ABD2
namespace ABCTriple

/-- The C-mask is additive. -/
theorem maskC_add
    (T : ABCTriple) (x y : T.FullTangent) :
    T.maskC (x + y) = T.maskC x + T.maskC y := by
  simp [ABCTriple.maskC]

/-- The C-mask is homogeneous. -/
theorem maskC_smul
    (T : ABCTriple) (k : ℤ) (x : T.FullTangent) :
    T.maskC (k • x) = k • T.maskC x := by
  simpa [ABCTriple.maskC] using
    (supportMask_smul T.support T.supportC k x)

/-- The C-mask commutes with subtraction. -/
theorem maskC_sub
    (T : ABCTriple) (x y : T.FullTangent) :
    T.maskC (x - y) = T.maskC x - T.maskC y := by
  simp [sub_eq_add_neg, ABCTriple.maskC]

/-- The C-linear form is additive. -/
theorem cLinearForm_add
    (T : ABCTriple) (x y : T.FullTangent) :
    T.cLinearForm (x + y) = T.cLinearForm x + T.cLinearForm y := by
  unfold ABCTriple.cLinearForm
  rw [T.maskC_add x y]
  rw [formalDeriv_add]

/-- The C-linear form is homogeneous. -/
theorem cLinearForm_smul
    (T : ABCTriple) (k : ℤ) (x : T.FullTangent) :
    T.cLinearForm (k • x) = k • T.cLinearForm x := by
  unfold ABCTriple.cLinearForm
  rw [T.maskC_smul k x]
  rw [formalDeriv_smul]
  rfl

/-- The C-linear form commutes with subtraction. -/
theorem cLinearForm_sub
    (T : ABCTriple) (x y : T.FullTangent) :
    T.cLinearForm (x - y) = T.cLinearForm x - T.cLinearForm y := by
  unfold ABCTriple.cLinearForm
  rw [T.maskC_sub x y]
  rw [formalDeriv_sub]

/-- The kernel of the C-linear form.  This is the direction space of a C-fiber. -/
def CKernel (T : ABCTriple) : Submodule ℤ T.FullTangent where
  carrier := {x | T.cLinearForm x = 0}
  zero_mem' := by
    unfold ABCTriple.cLinearForm
    simp [ABCTriple.maskC, formalDeriv_zero]
  add_mem' := by
    intro x y hx hy
    change T.cLinearForm (x + y) = 0
    rw [T.cLinearForm_add x y]
    rw [hx, hy]
    simp
  smul_mem' := by
    intro k x hx
    change T.cLinearForm (k • x) = 0
    rw [T.cLinearForm_smul k x]
    rw [hx]
    simp

@[simp]
theorem mem_CKernel_iff
    (T : ABCTriple) (x : T.FullTangent) :
    x ∈ T.CKernel ↔ T.cLinearForm x = 0 := by
  rfl

/-- Two C-lifts of the same seed have the same C-linear value. -/
theorem cLinearForm_eq_of_HasCLift_same_seed
    (T : ABCTriple) {seed lift₁ lift₂ : T.FullTangent}
    (h₁ : T.HasCLift seed lift₁) (h₂ : T.HasCLift seed lift₂) :
    T.cLinearForm lift₁ = T.cLinearForm lift₂ := by
  rw [h₁.c_balance, h₂.c_balance]

/-- The difference of two C-lifts of the same seed lies in the C-kernel.

This is the first fiber theorem: all lifts of a fixed seed live in one affine
coset of `CKernel`. -/
theorem sub_mem_CKernel_of_HasCLift_same_seed
    (T : ABCTriple) {seed lift₁ lift₂ : T.FullTangent}
    (h₁ : T.HasCLift seed lift₁) (h₂ : T.HasCLift seed lift₂) :
    lift₁ - lift₂ ∈ T.CKernel := by
  rw [T.mem_CKernel_iff]
  rw [T.cLinearForm_sub lift₁ lift₂]
  rw [T.cLinearForm_eq_of_HasCLift_same_seed h₁ h₂]
  simp

end ABCTriple
end ABD2
