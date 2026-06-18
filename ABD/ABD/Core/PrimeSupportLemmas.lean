import ABD.ABD.Core.SupportLemmas

namespace ABD

/-- A finite support whose entries are all prime numbers.

This is a Core-level predicate.  It deliberately says only that the chosen
Boolean support is prime-shaped; it does not mention tangent vectors,
derivatives, kernels, or smallness. -/
def PrimeSupport (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p ∈ S → Nat.Prime p

@[simp] theorem primeSupport_iff (S : Finset ℕ) :
    PrimeSupport S ↔ ∀ p : ℕ, p ∈ S → Nat.Prime p := by
  rfl

/-- A number is supported by a prime-shaped finite support. -/
def PrimeSupports (S : Finset ℕ) (n : ℕ) : Prop :=
  Supports S n ∧ PrimeSupport S

/-- The prime-shapedness predicate is monotone downward along support inclusion. -/
theorem PrimeSupport.mono {S T : Finset ℕ}
    (hT : PrimeSupport T) (hST : S ⊆ T) : PrimeSupport S := by
  intro p hp
  exact hT p (hST hp)

/-- The support attached to an ABC triple is prime-shaped when explicitly assumed so.

The arithmetic theorem that `ABCTriple.support` is automatically prime-shaped
from `Nat.factorization.support` belongs to the next support-arithmetic step.
This definition-level alias gives later layers a stable name to depend on
without importing derivative or lattice machinery. -/
def ABCTriple.HasPrimeSupport (T : ABCTriple) : Prop :=
  ABD.PrimeSupport T.support

@[simp] theorem ABCTriple.primeSupport_iff (T : ABCTriple) :
    T.HasPrimeSupport ↔ PrimeSupport T.support := by
  rfl

end ABD
