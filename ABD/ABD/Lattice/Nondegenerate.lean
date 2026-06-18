import ABD.ABD.Lattice.Smallness

namespace ABD

/-- A tangent vector is nonzero if at least one prime direction has nonzero value. -/
def NonzeroTangent (S : Finset ℕ) (x : Tangent S) : Prop :=
  ∃ hp : {p : ℕ // p ∈ S}, x hp ≠ 0

/-- First placeholder for nondegeneracy.

Later this should be strengthened to exclude the Pasten-style degenerate subspaces,
but `NonzeroTangent` is the right minimal first cut.
-/
def Nondegenerate (S : Finset ℕ) (x : Tangent S) : Prop :=
  NonzeroTangent S x

end ABD
