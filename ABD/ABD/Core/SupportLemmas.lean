import ABD.ABD.Core.TripleSupport

namespace ABD

/-- `S` contains the Boolean prime-support of `n`.

This predicate is deliberately Core-level: it only talks about the support
layer and does not mention tangent vectors or formal derivatives.
-/
def Supports (S : Finset ℕ) (n : ℕ) : Prop :=
  supp n ⊆ S

@[simp] theorem supports_iff (S : Finset ℕ) (n : ℕ) :
    Supports S n ↔ supp n ⊆ S := by
  rfl

/-- Support containment is monotone in the ambient support. -/
theorem Supports.mono {S T : Finset ℕ} {n : ℕ}
    (hn : Supports S n) (hST : S ⊆ T) : Supports T n := by
  intro p hp
  exact hST (hn hp)

/-- The support of the first component of a triple is contained in the
triple support. -/
theorem ABCTriple.supp_a_subset_support (T : ABCTriple) :
    supp T.a ⊆ T.support := by
  intro p hp
  simpa only [ABCTriple.support, Finset.mem_union] using
    (Or.inl hp :
      p ∈ supp T.a ∨ (p ∈ supp T.b ∨ p ∈ supp T.c))

/-- The support of the second component of a triple is contained in the
triple support. -/
theorem ABCTriple.supp_b_subset_support (T : ABCTriple) :
    supp T.b ⊆ T.support := by
  intro p hp
  simpa only [ABCTriple.support, Finset.mem_union] using
    (Or.inr (Or.inl hp) :
      p ∈ supp T.a ∨ (p ∈ supp T.b ∨ p ∈ supp T.c))

/-- The support of the third component of a triple is contained in the
triple support. -/
theorem ABCTriple.supp_c_subset_support (T : ABCTriple) :
    supp T.c ⊆ T.support := by
  intro p hp
  simpa only [ABCTriple.support, Finset.mem_union] using
    (Or.inr (Or.inr hp) :
      p ∈ supp T.a ∨ (p ∈ supp T.b ∨ p ∈ supp T.c))

/-- The triple support supports the first component. -/
theorem ABCTriple.supports_a (T : ABCTriple) :
    Supports T.support T.a :=
  T.supp_a_subset_support

/-- The triple support supports the second component. -/
theorem ABCTriple.supports_b (T : ABCTriple) :
    Supports T.support T.b :=
  T.supp_b_subset_support

/-- The triple support supports the third component. -/
theorem ABCTriple.supports_c (T : ABCTriple) :
    Supports T.support T.c :=
  T.supp_c_subset_support

/-- Bundled support coverage for all three entries of an additive triple. -/
theorem ABCTriple.supports_all (T : ABCTriple) :
    Supports T.support T.a ∧ Supports T.support T.b ∧ Supports T.support T.c :=
  ⟨T.supports_a, T.supports_b, T.supports_c⟩

end ABD
