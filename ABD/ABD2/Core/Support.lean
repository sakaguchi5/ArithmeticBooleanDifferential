import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Finset.Basic

namespace ABD2

/-- Prime support, implemented by mathlib's `Nat.factorization`. -/
def PrimeSupport (n : ℕ) : Finset ℕ :=
  n.factorization.support

/-- Alias used when the support is being treated as a Boolean object. -/
def BoolSupport (n : ℕ) : Finset ℕ :=
  PrimeSupport n

@[simp]
theorem BoolSupport_eq_PrimeSupport (n : ℕ) :
    BoolSupport n = PrimeSupport n := by
  rfl

/-- Boolean intersection of supports.  This is the AND operation. -/
def supportAnd (A B : Finset ℕ) : Finset ℕ :=
  A ∩ B

/-- Boolean union of supports. -/
def supportOr (A B : Finset ℕ) : Finset ℕ :=
  A ∪ B

/-- Boolean difference of supports. -/
def supportDiff (A B : Finset ℕ) : Finset ℕ :=
  A \ B

/-- Boolean XOR / symmetric difference, written without relying on a special API. -/
def supportXor (A B : Finset ℕ) : Finset ℕ :=
  (A \ B) ∪ (B \ A)

@[simp]
theorem mem_supportAnd_iff (p : ℕ) (A B : Finset ℕ) :
    p ∈ supportAnd A B ↔ p ∈ A ∧ p ∈ B := by
  simp [supportAnd]

@[simp]
theorem mem_supportOr_iff (p : ℕ) (A B : Finset ℕ) :
    p ∈ supportOr A B ↔ p ∈ A ∨ p ∈ B := by
  simp [supportOr]

@[simp]
theorem mem_supportDiff_iff (p : ℕ) (A B : Finset ℕ) :
    p ∈ supportDiff A B ↔ p ∈ A ∧ p ∉ B := by
  simp [supportDiff]

@[simp]
theorem mem_supportXor_iff (p : ℕ) (A B : Finset ℕ) :
    p ∈ supportXor A B ↔ (p ∈ A ∧ p ∉ B) ∨ (p ∈ B ∧ p ∉ A) := by
  simp [supportXor, and_comm]

end ABD2
