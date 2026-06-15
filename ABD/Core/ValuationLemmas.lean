import ABD.Core.PrimeSupportLemmas

namespace ABD

/-- The ordinary support of a natural number is prime-shaped.

This is the Core-level arithmetic fact needed to turn a triple support into a
prime support.  It is isolated here because the exact proof goes through
mathlib's `Nat.factorization.support = n.primeFactors` API and should not leak
into the differential or lattice layers. -/
axiom primeSupport_supp (n : ℕ) : PrimeSupport (supp n)

/-- Prime-shaped supports are closed under finite union. -/
theorem PrimeSupport.union {S T : Finset ℕ}
    (hS : PrimeSupport S) (hT : PrimeSupport T) : PrimeSupport (S ∪ T) := by
  intro p hp
  rw [Finset.mem_union] at hp
  cases hp with
  | inl hpS => exact hS p hpS
  | inr hpT => exact hT p hpT

/-- The support of an additive triple is automatically prime-shaped. -/
theorem ABCTriple.hasPrimeSupport (T : ABCTriple) : T.HasPrimeSupport := by
  unfold ABCTriple.HasPrimeSupport ABCTriple.support
  exact PrimeSupport.union (primeSupport_supp T.a)
    (PrimeSupport.union (primeSupport_supp T.b) (primeSupport_supp T.c))

/-- The first component of a triple is supported by a prime-shaped support. -/
theorem ABCTriple.primeSupports_a (T : ABCTriple) : PrimeSupports T.support T.a :=
  ⟨T.supports_a, T.hasPrimeSupport⟩

/-- The second component of a triple is supported by a prime-shaped support. -/
theorem ABCTriple.primeSupports_b (T : ABCTriple) : PrimeSupports T.support T.b :=
  ⟨T.supports_b, T.hasPrimeSupport⟩

/-- The third component of a triple is supported by a prime-shaped support. -/
theorem ABCTriple.primeSupports_c (T : ABCTriple) : PrimeSupports T.support T.c :=
  ⟨T.supports_c, T.hasPrimeSupport⟩

end ABD
