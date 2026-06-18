import ABD.ABD.Differential.Tangent

namespace ABD

/-- The `a`-side prime-support block of an additive triple. -/
def ABCTriple.supportA (T : ABCTriple) : Finset ℕ :=
  supp T.a

/-- The `b`-side prime-support block of an additive triple. -/
def ABCTriple.supportB (T : ABCTriple) : Finset ℕ :=
  supp T.b

/-- The `c`-side prime-support block of an additive triple. -/
def ABCTriple.supportC (T : ABCTriple) : Finset ℕ :=
  supp T.c

/-- The `a`-block is contained in the full Pasten support. -/
theorem ABCTriple.mem_supportA_support
    (T : ABCTriple) {p : ℕ} (hp : p ∈ T.supportA) :
    p ∈ T.support := by
  simp only [
    supportA,
    supp_eq_factorization_support,
    Nat.support_factorization,
    Nat.mem_primeFactors,
    ne_eq,
    support,
    Finset.mem_union
  ] at hp ⊢
  exact Or.inl hp

/-- The `b`-block is contained in the full Pasten support. -/
theorem ABCTriple.mem_supportB_support
    (T : ABCTriple) {p : ℕ} (hp : p ∈ T.supportB) :
    p ∈ T.support := by
  simp only [
    supportB,
    supp_eq_factorization_support,
    Nat.support_factorization,
    Nat.mem_primeFactors,
    ne_eq,
    support,
    Finset.mem_union
  ] at hp ⊢
  exact Or.inr (Or.inl hp)

/-- The `c`-block is contained in the full Pasten support. -/
theorem ABCTriple.mem_supportC_support
    (T : ABCTriple) {p : ℕ} (hp : p ∈ T.supportC) :
    p ∈ T.support := by
  simp only [
    supportC,
    supp_eq_factorization_support,
    Nat.support_factorization,
    Nat.mem_primeFactors,
    ne_eq,
    support,
    Finset.mem_union
  ] at hp ⊢
  exact Or.inr (Or.inr hp)

/-- Tangent vectors restricted to the `a`-support block. -/
abbrev ABCTriple.ATangent (T : ABCTriple) : Type :=
  Tangent T.supportA

/-- Tangent vectors restricted to the `b`-support block. -/
abbrev ABCTriple.BTangent (T : ABCTriple) : Type :=
  Tangent T.supportB

/-- Tangent vectors restricted to the `c`-support block. -/
abbrev ABCTriple.CTangent (T : ABCTriple) : Type :=
  Tangent T.supportC

/-- The `a`-block support is contained in the full Pasten support. -/
theorem ABCTriple.supportA_subset_support
    (T : ABCTriple) : T.supportA ⊆ T.support := by
  intro p hp
  exact T.mem_supportA_support hp

/-- The `b`-block support is contained in the full Pasten support. -/
theorem ABCTriple.supportB_subset_support
    (T : ABCTriple) : T.supportB ⊆ T.support := by
  intro p hp
  exact T.mem_supportB_support hp

/-- The `c`-block support is contained in the full Pasten support. -/
theorem ABCTriple.supportC_subset_support
    (T : ABCTriple) : T.supportC ⊆ T.support := by
  intro p hp
  exact T.mem_supportC_support hp

/-- Restrict a full tangent vector to the `a`-support block. -/
def ABCTriple.restrictA (T : ABCTriple) (x : Tangent T.support) : T.ATangent :=
  fun hp => x ⟨hp.1, T.supportA_subset_support hp.2⟩

/-- Restrict a full tangent vector to the `b`-support block. -/
def ABCTriple.restrictB (T : ABCTriple) (x : Tangent T.support) : T.BTangent :=
  fun hp => x ⟨hp.1, T.supportB_subset_support hp.2⟩

/-- Restrict a full tangent vector to the `c`-support block. -/
def ABCTriple.restrictC (T : ABCTriple) (x : Tangent T.support) : T.CTangent :=
  fun hp => x ⟨hp.1, T.supportC_subset_support hp.2⟩

@[simp]
theorem ABCTriple.restrictA_apply
    (T : ABCTriple) (x : Tangent T.support) (hp : {p : ℕ // p ∈ T.supportA}) :
    T.restrictA x hp = x ⟨hp.1, T.supportA_subset_support hp.2⟩ := by
  rfl

@[simp]
theorem ABCTriple.restrictB_apply
    (T : ABCTriple) (x : Tangent T.support) (hp : {p : ℕ // p ∈ T.supportB}) :
    T.restrictB x hp = x ⟨hp.1, T.supportB_subset_support hp.2⟩ := by
  rfl

@[simp]
theorem ABCTriple.restrictC_apply
    (T : ABCTriple) (x : Tangent T.support) (hp : {p : ℕ // p ∈ T.supportC}) :
    T.restrictC x hp = x ⟨hp.1, T.supportC_subset_support hp.2⟩ := by
  rfl

end ABD
