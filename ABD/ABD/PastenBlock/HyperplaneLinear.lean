import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import ABD.ABD.PastenBlock.Hyperplane

namespace ABD

open BigOperators

/-- The formal derivative is additive in the tangent vector.  This public local
version is used to package the restricted Wronskian as a linear map. -/
theorem formalDeriv_add_tangent
    (S : Finset ℕ) (x y : Tangent S) (n : ℕ) :
    formalDeriv S (x + y) n = formalDeriv S x n + formalDeriv S y n := by
  unfold formalDeriv
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The formal derivative is homogeneous in the tangent vector. -/
theorem formalDeriv_smul_tangent
    (S : Finset ℕ) (k : ℤ) (x : Tangent S) (n : ℕ) :
    formalDeriv S (k • x) n = k • formalDeriv S x n := by
  unfold formalDeriv
  calc
    (∑ hp : {p : ℕ // p ∈ S}, derivCoeff n hp.1 * (k • x) hp)
        = ∑ hp : {p : ℕ // p ∈ S}, k * (derivCoeff n hp.1 * x hp) := by
          apply Finset.sum_congr rfl
          intro hp _
          simp [Pi.smul_apply, mul_left_comm, mul_comm]
    _ = k * ∑ hp : {p : ℕ // p ∈ S}, derivCoeff n hp.1 * x hp := by
          simpa using
            (Finset.mul_sum
              (s := (Finset.univ : Finset {p : ℕ // p ∈ S}))
              (f := fun hp : {p : ℕ // p ∈ S} => derivCoeff n hp.1 * x hp)
              k).symm
    _ = k • ∑ hp : {p : ℕ // p ∈ S}, derivCoeff n hp.1 * x hp := by
          simp

/-- Additivity of the restricted `S_a ⊕ S_b` Wronskian form. -/
theorem ABCTriple.restrictedABWronskian_add
    (T : ABCTriple) (z w : T.ATangent × T.BTangent) :
    T.restrictedABWronskian (z.1 + w.1) (z.2 + w.2) =
      T.restrictedABWronskian z.1 z.2 + T.restrictedABWronskian w.1 w.2 := by
  unfold ABCTriple.restrictedABWronskian
  rw [formalDeriv_add_tangent]
  rw [formalDeriv_add_tangent]
  simp [mul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Homogeneity of the restricted `S_a ⊕ S_b` Wronskian form. -/
theorem ABCTriple.restrictedABWronskian_smul
    (T : ABCTriple) (k : ℤ) (z : T.ATangent × T.BTangent) :
    T.restrictedABWronskian (k • z.1) (k • z.2) =
      k • T.restrictedABWronskian z.1 z.2 := by
  unfold ABCTriple.restrictedABWronskian
  rw [formalDeriv_smul_tangent]
  rw [formalDeriv_smul_tangent]
  simp [mul_add, sub_eq_add_neg, mul_left_comm, mul_neg, add_comm]

/-- The restricted `S_a ⊕ S_b` Wronskian as an actual linear form. -/
noncomputable def ABCTriple.restrictedABWronskianLinear
    (T : ABCTriple) : ((T.ATangent × T.BTangent) →ₗ[ℤ] ℤ) where
  toFun z := T.restrictedABWronskian z.1 z.2
  map_add' := by
    intro z w
    exact T.restrictedABWronskian_add z w
  map_smul' := by
    intro k z
    exact T.restrictedABWronskian_smul k z

/-- The Wronskian hyperplane as a submodule: the kernel of the restricted
Wronskian linear form. -/
noncomputable def ABCTriple.ABWronskianHyperplaneSubmodule
    (T : ABCTriple) : Submodule ℤ (T.ATangent × T.BTangent) :=
  (T.restrictedABWronskianLinear).ker

@[simp]
theorem ABCTriple.mem_ABWronskianHyperplaneSubmodule_iff
    (T : ABCTriple) (z : T.ATangent × T.BTangent) :
    z ∈ T.ABWronskianHyperplaneSubmodule ↔
      T.restrictedABWronskian z.1 z.2 = 0 := by
  change T.restrictedABWronskianLinear z = 0 ↔
    T.restrictedABWronskian z.1 z.2 = 0
  rfl

/-- The earlier set-level hyperplane is exactly the carrier of the linear-map
kernel. -/
theorem ABCTriple.ABWronskianHyperplane_eq_submodule_carrier
    (T : ABCTriple) :
    T.ABWronskianHyperplane =
      (T.ABWronskianHyperplaneSubmodule : Set (T.ATangent × T.BTangent)) := by
  ext z
  rfl

/-- The `a/b` nondegenerate seed condition is avoidance of the linear kernel. -/
theorem ABCTriple.abWronskianNondegenerate_iff_not_mem_hyperplaneSubmodule
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) :
    T.ABWronskianNondegenerate xA xB ↔
      (xA, xB) ∉ T.ABWronskianHyperplaneSubmodule := by
  unfold ABCTriple.ABWronskianNondegenerate ABCTriple.ABWronskianHyperplaneSubmodule
  simp [ABCTriple.restrictedABWronskianLinear]

end ABD
