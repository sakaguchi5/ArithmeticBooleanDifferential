import ABD.ABD2.Module.SupportSubmodule

namespace ABD2

/-- The Boolean projection associated to a support mask. -/
noncomputable def Projection (S M : Finset ℕ) : Tangent S →ₗ[ℤ] Tangent S :=
  supportMaskLinear S M

@[simp]
theorem Projection_apply (S M : Finset ℕ) (x : Tangent S) :
    Projection S M x = supportMask S M x := by
  rfl

/-- Projection idempotence in linear-map form. -/
theorem Projection_idempotent (S M : Finset ℕ) :
    (Projection S M).comp (Projection S M) = Projection S M := by
  ext x p
  simp [Projection, supportMask_idempotent]

/-- Projection composition is Boolean AND. -/
theorem Projection_comp (S M N : Finset ℕ) :
    (Projection S M).comp (Projection S N) = Projection S (M ∩ N) := by
  ext x p
  simp [Projection, supportMask_comp]

/-- The range of a projection lies in the corresponding supported submodule. -/
theorem Projection_apply_mem_SupportedIn
    (S M : Finset ℕ) (x : Tangent S) :
    Projection S M x ∈ SupportedIn S M := by
  exact supportMask_mem_SupportedIn S M x

/-- A vector is fixed by the projection iff it is supported in the mask. -/
theorem Projection_eq_self_iff_mem_SupportedIn
    (S M : Finset ℕ) (x : Tangent S) :
    Projection S M x = x ↔ x ∈ SupportedIn S M := by
  constructor
  · intro h
    exact (mem_SupportedIn_iff_supportMask_eq_self S M x).2 h
  · intro h
    exact (mem_SupportedIn_iff_supportMask_eq_self S M x).1 h

end ABD2
