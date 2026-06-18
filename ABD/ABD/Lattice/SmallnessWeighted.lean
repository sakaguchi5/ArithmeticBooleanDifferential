import ABD.ABD.Lattice.SmallnessAbs

namespace ABD

/-- A weight function on the finite prime-support coordinates.  Keeping this
as an abbreviation makes the later geometry-of-numbers layer independent of
whether weights are eventually integers, logarithmic real weights, or some
other support-sensitive size model. -/
abbrev TangentWeight (S : Finset ℕ) : Type :=
  {p : ℕ // p ∈ S} → ℤ

/-- The constant weight `1` on a finite support. -/
def unitWeight (S : Finset ℕ) : TangentWeight S :=
  fun _ => 1

/-- Weighted absolute coordinate boundedness.

Read this as a future hook for support-sensitive size conditions: each tangent
coordinate is first scaled by a chosen weight and then bounded in absolute
value.
-/
def WeightedCoordinateAbsBounded
    (S : Finset ℕ) (w : TangentWeight S) (x : Tangent S) (B : ℤ) : Prop :=
  ∀ hp : {p : ℕ // p ∈ S}, |w hp * x hp| ≤ B

/-- Early weighted smallness predicate.  This is deliberately just an alias for
now; later layers can refine it into a norm or convex-body condition without
changing callers. -/
def WeightedSmallTangent
    (S : Finset ℕ) (w : TangentWeight S) (x : Tangent S) (B : ℤ) : Prop :=
  WeightedCoordinateAbsBounded S w x B

/-- With unit weights, weighted boundedness is exactly absolute coordinate
boundedness. -/
theorem weightedCoordinateAbsBounded_unit_iff_coordinateAbsBounded
    (S : Finset ℕ) (x : Tangent S) (B : ℤ) :
    WeightedCoordinateAbsBounded S (unitWeight S) x B ↔
      CoordinateAbsBounded S x B := by
  constructor
  · intro h hp
    simpa [WeightedCoordinateAbsBounded, unitWeight] using h hp
  · intro h hp
    simpa [WeightedCoordinateAbsBounded, unitWeight] using h hp

/-- With unit weights, weighted smallness is equivalent to the current
`SmallTangent` predicate. -/
theorem weightedSmallTangent_unit_iff_smallTangent
    (S : Finset ℕ) (x : Tangent S) (B : ℤ) :
    WeightedSmallTangent S (unitWeight S) x B ↔ SmallTangent S x B := by
  rw [WeightedSmallTangent,
    weightedCoordinateAbsBounded_unit_iff_coordinateAbsBounded,
    coordinateAbsBounded_iff_smallTangent]

/-- The zero tangent is weighted-small for every weight, as soon as the bound is
nonnegative. -/
@[simp] theorem weightedCoordinateAbsBounded_zeroTangent
    (S : Finset ℕ) (w : TangentWeight S) {B : ℤ} (hB : 0 ≤ B) :
    WeightedCoordinateAbsBounded S w (zeroTangent S) B := by
  intro hp
  simpa [WeightedCoordinateAbsBounded, zeroTangent] using hB

@[simp] theorem weightedSmallTangent_zeroTangent
    (S : Finset ℕ) (w : TangentWeight S) {B : ℤ} (hB : 0 ≤ B) :
    WeightedSmallTangent S w (zeroTangent S) B := by
  simpa [WeightedSmallTangent] using
    (weightedCoordinateAbsBounded_zeroTangent S w hB)

end ABD
