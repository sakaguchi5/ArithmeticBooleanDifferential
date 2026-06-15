import ABD.Core.PrimeSupportLemmas

namespace ABD

/-- The ordinary support of a natural number is prime-shaped.

This removes the Core-level arithmetic axiom: `supp n` is definitionally the
support of `Nat.factorization n`, and mathlib identifies that support with
`n.primeFactors`, whose members are prime. -/
theorem primeSupport_supp (n : ℕ) : PrimeSupport (supp n) := by
  intro p hp
  rw [supp, Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp

/-- If `p` does not divide `n`, its valuation in `n` is zero. -/
theorem val_eq_zero_of_not_dvd {n p : ℕ} (h : ¬ p ∣ n) : val n p = 0 := by
  unfold val
  exact Nat.factorization_eq_zero_of_not_dvd h

/-- If both factors are nonzero, valuations add across multiplication. -/
theorem val_mul_of_ne_zero {m n p : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    val (m * n) p = val m p + val n p := by
  unfold val
  have h := congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_mul hm hn)
  simpa using h

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
