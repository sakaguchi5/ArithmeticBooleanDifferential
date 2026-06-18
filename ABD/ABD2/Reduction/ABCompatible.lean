import ABD.ABD2.Reduction.CImage

namespace ABD2
namespace ABCTriple

/-- The A-mask is additive. -/
theorem maskA_add
    (T : ABCTriple) (x y : T.FullTangent) :
    T.maskA (x + y) = T.maskA x + T.maskA y := by
  simp [ABCTriple.maskA]

/-- The B-mask is additive. -/
theorem maskB_add
    (T : ABCTriple) (x y : T.FullTangent) :
    T.maskB (x + y) = T.maskB x + T.maskB y := by
  simp [ABCTriple.maskB]

/-- The AB target is additive in the full tangent variable. -/
theorem abTarget_add
    (T : ABCTriple) (x y : T.FullTangent) :
    T.abTarget (x + y) = T.abTarget x + T.abTarget y := by
  unfold ABCTriple.abTarget
  rw [T.maskA_add x y]
  rw [T.maskB_add x y]
  rw [formalDeriv_add]
  rw [formalDeriv_add]
  simp [add_assoc, add_left_comm, add_comm]

/-- The A-mask is homogeneous. -/
theorem maskA_smul
    (T : ABCTriple) (k : ℤ) (x : T.FullTangent) :
    T.maskA (k • x) = k • T.maskA x := by
  simpa [ABCTriple.maskA] using
    (supportMask_smul T.support T.supportA k x)

/-- The B-mask is homogeneous. -/
theorem maskB_smul
    (T : ABCTriple) (k : ℤ) (x : T.FullTangent) :
    T.maskB (k • x) = k • T.maskB x := by
  simpa [ABCTriple.maskB] using
    (supportMask_smul T.support T.supportB k x)

/-- The AB target is homogeneous in the full tangent variable. -/
theorem abTarget_smul
    (T : ABCTriple) (k : ℤ) (x : T.FullTangent) :
    T.abTarget (k • x) = k • T.abTarget x := by
  unfold ABCTriple.abTarget
  rw [T.maskA_smul k x]
  rw [T.maskB_smul k x]
  rw [formalDeriv_smul]
  rw [formalDeriv_smul]
  simp [mul_add]

@[simp]
theorem Wronskian_zero
    (T : ABCTriple) :
    T.Wronskian (0 : T.FullTangent) = 0 := by
  unfold Wronskian
  simp [formalDeriv_zero]

/-- Full tangents whose AB target is compatible with the chosen C-image profile. -/
def ABCompatibleSubmodule (T : ABCTriple) (P : T.CImageProfile) :
    Submodule ℤ T.FullTangent where
  carrier := {x | P.gcd ∣ T.abTarget x}
  zero_mem' := by
    unfold abTarget
    simp [ABCTriple.maskA, ABCTriple.maskB, formalDeriv_zero]
  add_mem' := by
    intro x y hx hy
    change P.gcd ∣ T.abTarget (x + y)
    rw [T.abTarget_add x y]
    exact dvd_add hx hy
  smul_mem' := by
    intro k x hx
    change P.gcd ∣ T.abTarget (k • x)
    rw [T.abTarget_smul k x]
    exact dvd_mul_of_dvd_right hx k

@[simp]
theorem mem_ABCompatibleSubmodule_iff
    (T : ABCTriple) (P : T.CImageProfile) (x : T.FullTangent) :
    x ∈ T.ABCompatibleSubmodule P ↔ P.gcd ∣ T.abTarget x := by
  rfl

/-- The Wronskian is additive in the tangent variable. -/
theorem Wronskian_add
    (T : ABCTriple) (x y : T.FullTangent) :
    T.Wronskian (x + y) = T.Wronskian x + T.Wronskian y := by
  unfold Wronskian
  rw [formalDeriv_add]
  rw [formalDeriv_add]
  simp [mul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- The Wronskian is homogeneous in the tangent variable. -/
theorem Wronskian_smul
    (T : ABCTriple) (k : ℤ) (x : T.FullTangent) :
    T.Wronskian (k • x) = k • T.Wronskian x := by
  unfold Wronskian
  rw [formalDeriv_smul]
  rw [formalDeriv_smul]
  simp [mul_sub, mul_left_comm]

/-- The Wronskian-degenerate hyperplane as a submodule. -/
def ABWronskianKernel (T : ABCTriple) : Submodule ℤ T.FullTangent where
  carrier := {x | T.Wronskian x = 0}
  zero_mem' := by
    unfold Wronskian
    simp [formalDeriv_zero]
  add_mem' := by
    intro x y hx hy
    change T.Wronskian (x + y) = 0
    rw [T.Wronskian_add x y]
    rw [hx, hy]
    simp
  smul_mem' := by
    intro k x hx
    change T.Wronskian (k • x) = 0
    rw [T.Wronskian_smul k x]
    rw [hx]
    simp

@[simp]
theorem mem_ABWronskianKernel_iff
    (T : ABCTriple) (x : T.FullTangent) :
    x ∈ T.ABWronskianKernel ↔ T.Wronskian x = 0 := by
  rfl

/-- First bad-seed predicate: every C-compatible AB seed is Wronskian-degenerate. -/
def BadSeed (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  T.ABCompatibleSubmodule P ≤ T.ABWronskianKernel

/-- The complementary good-seed predicate. -/
def HasGoodABSeed (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  ∃ x : T.FullTangent, x ∈ T.ABCompatibleSubmodule P ∧ x ∉ T.ABWronskianKernel

/-- Good AB seed is exactly failure of the first bad-seed inclusion. -/
theorem hasGoodABSeed_iff_not_BadSeed
    (T : ABCTriple) (P : T.CImageProfile) :
    T.HasGoodABSeed P ↔ ¬ T.BadSeed P := by
  constructor
  · intro h hbad
    rcases h with ⟨x, hx, hnot⟩
    exact hnot (hbad hx)
  · intro hnot
    by_contra hno
    apply hnot
    intro x hx
    by_contra hxnot
    exact hno ⟨x, hx, hxnot⟩

end ABCTriple
end ABD2
