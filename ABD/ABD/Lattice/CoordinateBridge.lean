import ABD.ABD.Lattice.PastenCandidate

namespace ABD

/-- The current coordinate representation of a tangent vector.

This is deliberately a no-op bridge: `Tangent S` is already a coordinate
function on the subtype of primes in `S`.  A later bridge to `Fin S.card → ℤ`
can refine this file without changing the lower layers. -/
abbrev SubtypeCoordinateTangent (S : Finset ℕ) : Type :=
  {p : ℕ // p ∈ S} → ℤ

/-- View a tangent vector as its current subtype-coordinate function. -/
def Tangent.toSubtypeCoordinates (S : Finset ℕ) (x : Tangent S) :
    SubtypeCoordinateTangent S :=
  x

/-- Rebuild a tangent vector from the current subtype-coordinate function. -/
def Tangent.ofSubtypeCoordinates (S : Finset ℕ)
    (x : SubtypeCoordinateTangent S) : Tangent S :=
  x

@[simp] theorem Tangent.of_toSubtypeCoordinates
    (S : Finset ℕ) (x : Tangent S) :
    Tangent.ofSubtypeCoordinates S (Tangent.toSubtypeCoordinates S x) = x := by
  rfl

@[simp] theorem Tangent.to_ofSubtypeCoordinates
    (S : Finset ℕ) (x : SubtypeCoordinateTangent S) :
    Tangent.toSubtypeCoordinates S (Tangent.ofSubtypeCoordinates S x) = x := by
  rfl

end ABD
