import ABD.Differential.All

namespace ABD

/-- The additive kernel attached to the selected equation `a + b = c`.

At this early stage this is just a set of tangent vectors.  Later it can be
upgraded to a genuine `Submodule` once the linear algebra layer is worth paying for.
-/
def AdditiveKernel (S : Finset ℕ) (a b c : ℕ) : Set (Tangent S) :=
  {x | AdditiveOn S x a b c}

@[simp]
theorem mem_additiveKernel_iff
    (S : Finset ℕ) (x : Tangent S) (a b c : ℕ) :
    x ∈ AdditiveKernel S a b c ↔ AdditiveOn S x a b c := by
  rfl

end ABD
