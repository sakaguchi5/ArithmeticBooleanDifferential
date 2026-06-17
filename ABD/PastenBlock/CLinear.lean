import Mathlib.Algebra.Module.LinearMap.Defs
import ABD.PastenBlock.Adjustment
import ABD.PastenBlock.HyperplaneLinear

namespace ABD

/-- Additivity of the `c`-side adjustment form. -/
theorem ABCTriple.cLinearForm_add
    (T : ABCTriple) (x y : T.CTangent) :
    T.cLinearForm (x + y) = T.cLinearForm x + T.cLinearForm y := by
  unfold ABCTriple.cLinearForm
  rw [formalDeriv_add_tangent]

/-- Homogeneity of the `c`-side adjustment form. -/
theorem ABCTriple.cLinearForm_smul
    (T : ABCTriple) (k : ℤ) (x : T.CTangent) :
    T.cLinearForm (k • x) = k • T.cLinearForm x := by
  unfold ABCTriple.cLinearForm
  rw [formalDeriv_smul_tangent]

/-- The `c`-side adjustment map as an actual integer linear map.

This packages `L_c : ℤ^{S_c} → ℤ` so that the next layer can speak about its
range/image rather than only the set-level predicate `cImage`. -/
noncomputable def ABCTriple.cLinearMap
    (T : ABCTriple) : T.CTangent →ₗ[ℤ] ℤ where
  toFun := T.cLinearForm
  map_add' := by
    intro x y
    exact T.cLinearForm_add x y
  map_smul' := by
    intro k x
    exact T.cLinearForm_smul k x

@[simp]
theorem ABCTriple.cLinearMap_apply
    (T : ABCTriple) (xC : T.CTangent) :
    T.cLinearMap xC = T.cLinearForm xC := by
  rfl

end ABD
