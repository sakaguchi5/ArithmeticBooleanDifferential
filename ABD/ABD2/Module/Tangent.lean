import ABD.ABD2.Core.All

namespace ABD2

/-- The tangent module on a finite prime support. -/
abbrev TangentModule (S : Finset ℕ) := Tangent S

/-- Coordinate evaluation on the tangent module. -/
def coord (S : Finset ℕ) (p : {p : ℕ // p ∈ S}) : Tangent S →ₗ[ℤ] ℤ where
  toFun x := x p
  map_add' := by intro x y; rfl
  map_smul' := by intro k x; rfl

@[simp]
theorem coord_apply (S : Finset ℕ) (p : {p : ℕ // p ∈ S}) (x : Tangent S) :
    coord S p x = x p := by
  rfl

end ABD2
