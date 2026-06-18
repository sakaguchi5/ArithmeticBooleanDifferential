import ABD.ABD2.Core.Support
import Mathlib.Algebra.Module.LinearMap.Defs

namespace ABD2

/-- A tangent vector on the finite prime support `S`.

The coordinate at `p : S` is the value assigned to the prime direction `p`. -/
abbrev Tangent (S : Finset ℕ) : Type :=
  {p : ℕ // p ∈ S} → ℤ

/-- Boolean mask action on `ℤ^S`.

`supportMask S M x` keeps the coordinates whose underlying prime lies in `M`
and kills the complementary coordinates.  The mask `M` is allowed to be any
finite set; only its intersection with `S` matters. -/
def supportMask (S M : Finset ℕ) (x : Tangent S) : Tangent S :=
  fun p => if p.1 ∈ M then x p else 0

@[simp]
theorem supportMask_apply_mem
    (S M : Finset ℕ) (x : Tangent S) (p : {p : ℕ // p ∈ S})
    (hp : p.1 ∈ M) :
    supportMask S M x p = x p := by
  simp [supportMask, hp]

@[simp]
theorem supportMask_apply_not_mem
    (S M : Finset ℕ) (x : Tangent S) (p : {p : ℕ // p ∈ S})
    (hp : p.1 ∉ M) :
    supportMask S M x p = 0 := by
  simp [supportMask, hp]

@[simp]
theorem supportMask_empty (S : Finset ℕ) (x : Tangent S) :
    supportMask S ∅ x = 0 := by
  funext p
  simp [supportMask]

@[simp]
theorem supportMask_univ_on_support (S : Finset ℕ) (x : Tangent S) :
    supportMask S S x = x := by
  funext p
  simp [supportMask, p.2]

@[simp]
theorem supportMask_zero (S M : Finset ℕ) :
    supportMask S M (0 : Tangent S) = 0 := by
  funext p
  by_cases hp : p.1 ∈ M <;> simp [supportMask, hp]

@[simp]
theorem supportMask_add (S M : Finset ℕ) (x y : Tangent S) :
    supportMask S M (x + y) = supportMask S M x + supportMask S M y := by
  funext p
  by_cases hp : p.1 ∈ M <;> simp [supportMask, hp]

@[simp]
theorem supportMask_neg (S M : Finset ℕ) (x : Tangent S) :
    supportMask S M (-x) = -supportMask S M x := by
  funext p
  by_cases hp : p.1 ∈ M <;> simp [supportMask, hp]

@[simp]
theorem supportMask_sub (S M : Finset ℕ) (x y : Tangent S) :
    supportMask S M (x - y) = supportMask S M x - supportMask S M y := by
  funext p
  by_cases hp : p.1 ∈ M <;> simp [supportMask, hp]

@[simp]
theorem supportMask_smul (S M : Finset ℕ) (k : ℤ) (x : Tangent S) :
    supportMask S M (k • x) = k • supportMask S M x := by
  funext p
  by_cases hp : p.1 ∈ M <;> simp [supportMask, hp]

/-- The mask as a linear endomorphism of the tangent module. -/
noncomputable def supportMaskLinear (S M : Finset ℕ) :
    Tangent S →ₗ[ℤ] Tangent S where
  toFun := supportMask S M
  map_add' := by
    intro x y
    exact supportMask_add S M x y
  map_smul' := by
    intro k x
    exact supportMask_smul S M k x

@[simp]
theorem supportMaskLinear_apply
    (S M : Finset ℕ) (x : Tangent S) :
    supportMaskLinear S M x = supportMask S M x := by
  rfl

end ABD2
