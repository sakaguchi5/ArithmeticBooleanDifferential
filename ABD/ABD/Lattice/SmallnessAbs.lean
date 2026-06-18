import ABD.ABD.Lattice.Smallness
import Mathlib.Algebra.Order.Group.Abs

namespace ABD

/-- Absolute-value form of coordinatewise boundedness.

This is the geometry-of-numbers friendly presentation of the current
coordinatewise smallness predicate.  It is definitionally separate from
`SmallTangent` so later norm/sup-norm layers can refer to the absolute-value
form without changing the original placeholder predicate.
-/
def CoordinateAbsBounded (S : Finset ℕ) (x : Tangent S) (B : ℤ) : Prop :=
  ∀ hp : {p : ℕ // p ∈ S}, |x hp| ≤ B

/-- The current coordinatewise smallness predicate is equivalent to the
absolute-value version. -/
theorem coordinateAbsBounded_iff_smallTangent
    (S : Finset ℕ) (x : Tangent S) (B : ℤ) :
    CoordinateAbsBounded S x B ↔ SmallTangent S x B := by
  constructor
  · intro h hp
    exact abs_le.mp (h hp)
  · intro h hp
    exact abs_le.mpr (h hp)

/-- A direct wrapper from absolute-value boundedness to the existing
`SmallTangent` predicate. -/
theorem smallTangent_of_coordinateAbsBounded
    {S : Finset ℕ} {x : Tangent S} {B : ℤ}
    (h : CoordinateAbsBounded S x B) :
    SmallTangent S x B :=
  (coordinateAbsBounded_iff_smallTangent S x B).mp h

/-- A direct wrapper from the existing `SmallTangent` predicate to the
absolute-value form. -/
theorem coordinateAbsBounded_of_smallTangent
    {S : Finset ℕ} {x : Tangent S} {B : ℤ}
    (h : SmallTangent S x B) :
    CoordinateAbsBounded S x B :=
  (coordinateAbsBounded_iff_smallTangent S x B).mpr h

@[simp] theorem coordinateAbsBounded_zeroTangent
    (S : Finset ℕ) {B : ℤ} (hB : 0 ≤ B) :
    CoordinateAbsBounded S (zeroTangent S) B := by
  intro hp
  simpa [CoordinateAbsBounded, zeroTangent] using hB

end ABD
