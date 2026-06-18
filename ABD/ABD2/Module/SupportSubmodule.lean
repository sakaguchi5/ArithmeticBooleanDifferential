import ABD.ABD2.Module.Tangent
import Mathlib.Algebra.Module.Submodule.Basic

namespace ABD2

/-- Tangent vectors supported inside a Boolean mask `M`. -/
def SupportedIn (S M : Finset ℕ) : Submodule ℤ (Tangent S) where
  carrier := {x | ∀ p : {p : ℕ // p ∈ S}, p.1 ∉ M → x p = 0}
  zero_mem' := by
    intro p hp
    rfl
  add_mem' := by
    intro x y hx hy p hp
    simp [hx p hp, hy p hp]
  smul_mem' := by
    intro k x hx p hp
    simp [hx p hp]

@[simp]
theorem mem_SupportedIn_iff
    (S M : Finset ℕ) (x : Tangent S) :
    x ∈ SupportedIn S M ↔
      ∀ p : {p : ℕ // p ∈ S}, p.1 ∉ M → x p = 0 := by
  rfl

/-- Masking by `M` produces a vector supported in `M`. -/
theorem supportMask_mem_SupportedIn
    (S M : Finset ℕ) (x : Tangent S) :
    supportMask S M x ∈ SupportedIn S M := by
  intro p hp
  simp [supportMask, hp]

/-- A vector is supported in `M` iff masking by `M` fixes it. -/
theorem mem_SupportedIn_iff_supportMask_eq_self
    (S M : Finset ℕ) (x : Tangent S) :
    x ∈ SupportedIn S M ↔ supportMask S M x = x := by
  constructor
  · intro hx
    funext p
    by_cases hp : p.1 ∈ M
    · simp [supportMask, hp]
    · simp [supportMask, hp, hx p hp]
  · intro h p hp
    have hcoord := congrFun h p
    simpa [supportMask, hp] using hcoord.symm

/-- If `M ⊆ N`, then vectors supported in `M` are supported in `N`. -/
theorem SupportedIn_mono
    (S M N : Finset ℕ) (hMN : M ⊆ N) :
    SupportedIn S M ≤ SupportedIn S N := by
  intro x hx p hpN
  exact hx p (fun hpM => hpN (hMN hpM))

end ABD2
