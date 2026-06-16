import Mathlib.Algebra.Module.Submodule.Basic
import ABD.Lattice.KernelClosure

namespace ABD

/-- The additive kernel as an actual `ℤ`-submodule of the tangent space.

The underlying carrier is the previously defined set-level `AdditiveKernel`.
The proof fields are supplied by the closure lemmas in `KernelClosure`.
-/
def AdditiveKernelSubmodule
    (S : Finset ℕ) (a b c : ℕ) : Submodule ℤ (Tangent S) where
  carrier := AdditiveKernel S a b c
  zero_mem' := zero_mem_additiveKernel S a b c
  add_mem' := by
    intro x y hx hy
    exact add_mem_additiveKernel hx hy
  smul_mem' := by
    intro k x hx
    exact zsmul_mem_additiveKernel k hx

/-- Membership in the submodule version is the original additive condition. -/
@[simp] theorem mem_additiveKernelSubmodule_iff
    (S : Finset ℕ) (x : Tangent S) (a b c : ℕ) :
    x ∈ AdditiveKernelSubmodule S a b c ↔ AdditiveOn S x a b c := by
  change x ∈ AdditiveKernel S a b c ↔ AdditiveOn S x a b c
  rfl

/-- The submodule carrier is definitionally the set-level additive kernel. -/
@[simp] theorem additiveKernelSubmodule_carrier
    (S : Finset ℕ) (a b c : ℕ) :
    ((AdditiveKernelSubmodule S a b c : Set (Tangent S)) =
      AdditiveKernel S a b c) := by
  rfl

/-- The additive kernel attached to an additive triple as a `ℤ`-submodule. -/
def TripleAdditiveKernelSubmodule
    (T : ABCTriple) : Submodule ℤ (Tangent T.support) where
  carrier := TripleAdditiveKernel T
  zero_mem' := zero_mem_tripleAdditiveKernel T
  add_mem' := by
    intro x y hx hy
    exact add_mem_tripleAdditiveKernel hx hy
  smul_mem' := by
    intro k x hx
    exact zsmul_mem_tripleAdditiveKernel k hx

/-- Membership in the triple submodule is the triple additive condition. -/
@[simp] theorem mem_tripleAdditiveKernelSubmodule_iff
    (T : ABCTriple) (x : Tangent T.support) :
    x ∈ TripleAdditiveKernelSubmodule T ↔
      AdditiveOn T.support x T.a T.b T.c := by
  change x ∈ TripleAdditiveKernel T ↔
    AdditiveOn T.support x T.a T.b T.c
  rfl

/-- The triple submodule carrier is definitionally the set-level triple kernel. -/
@[simp] theorem tripleAdditiveKernelSubmodule_carrier
    (T : ABCTriple) :
    ((TripleAdditiveKernelSubmodule T : Set (Tangent T.support)) =
      TripleAdditiveKernel T) := by
  rfl

end ABD
