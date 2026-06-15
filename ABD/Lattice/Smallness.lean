import ABD.Lattice.Kernel

namespace ABD

/-- Coordinatewise boundedness for a tangent vector.

This is only a placeholder for the future geometry-of-numbers layer.  It avoids norms
for now and keeps smallness as a simple coordinate condition.
-/
def CoordinateBounded (S : Finset ℕ) (x : Tangent S) (B : ℤ) : Prop :=
  ∀ hp : {p : ℕ // p ∈ S}, -B ≤ x hp ∧ x hp ≤ B

/-- Early smallness predicate for tangent vectors. -/
def SmallTangent (S : Finset ℕ) (x : Tangent S) (B : ℤ) : Prop :=
  CoordinateBounded S x B

end ABD
