import ABD.ABD2.Fibration.TargetZero
import ABD.ABD2.Fibration.FiniteBound

namespace ABD2
namespace ABCTriple

/-- The AB part of a full tangent.

B1 separates the two-sided target-zero construction from the C-lift problem.  The
cost we want to watch first is the coordinate size of the A/B part, not the C
part. -/
def ABPart (T : ABCTriple) (x : T.FullTangent) : T.FullTangent :=
  T.maskA x + T.maskB x

@[simp]
theorem ABPart_apply
    (T : ABCTriple) (x : T.FullTangent) :
    T.ABPart x = T.maskA x + T.maskB x := by
  rfl

/-- Coordinatewise AB-smallness for a full tangent.

This deliberately measures only the A/B projection `maskA x + maskB x`.  Thus a
B1 bound records the cost of making the AB target cancel, before any C-side lift
or gauge optimization is considered. -/
def ABSmallTangent (T : ABCTriple) (x : T.FullTangent) (B : ℤ) : Prop :=
  T.SmallTangent (T.ABPart x) B

/-- A crude finite AB coordinate bound, obtained by applying the existing finite
coordinate bound to the AB part of the tangent. -/
noncomputable def abCoordinateBound
    (T : ABCTriple) (x : T.FullTangent) : ℤ :=
  T.coordinateBound (T.ABPart x)

/-- Every tangent is AB-small for its crude AB coordinate bound. -/
theorem abSmallTangent_abCoordinateBound
    (T : ABCTriple) (x : T.FullTangent) :
    T.ABSmallTangent x (T.abCoordinateBound x) := by
  exact T.smallTangent_coordinateBound (T.ABPart x)

/-- A target-zero good base point with an explicit AB coordinate bound. -/
def TargetZeroGoodBasePointAtMost
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) : Prop :=
  ∃ x : T.FullTangent,
    T.TargetZeroGoodBasePoint P x ∧ T.ABSmallTangent x B

/-- Existence of some finite AB cost for a target-zero good base point. -/
def HasFiniteTargetZeroABCost
    (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  ∃ B : ℤ, T.TargetZeroGoodBasePointAtMost P B

/-- The explicit witness form of a bounded target-zero AB cost. -/
theorem targetZeroGoodBasePointAtMost_of_targetZeroGoodBasePoint
    (T : ABCTriple) (P : T.CImageProfile) {x : T.FullTangent}
    (h : T.TargetZeroGoodBasePoint P x) :
    T.TargetZeroGoodBasePointAtMost P (T.abCoordinateBound x) := by
  exact ⟨x, h, T.abSmallTangent_abCoordinateBound x⟩

/-- A target-zero good base point automatically has finite AB cost. -/
theorem hasFiniteTargetZeroABCost_of_hasTargetZeroGoodBasePoint
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasTargetZeroGoodBasePoint P) :
    T.HasFiniteTargetZeroABCost P := by
  rcases h with ⟨x, hx⟩
  exact ⟨T.abCoordinateBound x,
    T.targetZeroGoodBasePointAtMost_of_targetZeroGoodBasePoint P hx⟩

/-- A bounded target-zero AB-cost point is, in particular, a target-zero good base
point. -/
theorem hasTargetZeroGoodBasePoint_of_targetZeroGoodBasePointAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.TargetZeroGoodBasePointAtMost P B) :
    T.HasTargetZeroGoodBasePoint P := by
  rcases h with ⟨x, hx, _hsmall⟩
  exact ⟨x, hx⟩

/-- Finite target-zero AB cost implies the qualitative target-zero B0 object. -/
theorem hasTargetZeroGoodBasePoint_of_hasFiniteTargetZeroABCost
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasFiniteTargetZeroABCost P) :
    T.HasTargetZeroGoodBasePoint P := by
  rcases h with ⟨B, hB⟩
  exact T.hasTargetZeroGoodBasePoint_of_targetZeroGoodBasePointAtMost P hB

/-- A bounded target-zero AB-cost point is, in particular, a good base point. -/
theorem hasGoodBasePoint_of_targetZeroGoodBasePointAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.TargetZeroGoodBasePointAtMost P B) :
    T.HasGoodBasePoint P := by
  exact T.hasGoodBasePoint_of_hasTargetZeroGoodBasePoint P
    (T.hasTargetZeroGoodBasePoint_of_targetZeroGoodBasePointAtMost P h)

/-- Finite target-zero AB cost implies the usual good-base condition. -/
theorem hasGoodBasePoint_of_hasFiniteTargetZeroABCost
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasFiniteTargetZeroABCost P) :
    T.HasGoodBasePoint P := by
  exact T.hasGoodBasePoint_of_hasTargetZeroGoodBasePoint P
    (T.hasTargetZeroGoodBasePoint_of_hasFiniteTargetZeroABCost P h)

/-- B1 finite-cost consequence of B0: in the two-sided support case, the
AB-cancellation cost is finite.

This does not claim a power-saving estimate.  It records the structural outcome
of B0 in cost language: once a target-zero good base point exists, its A/B part
has some finite coordinate bound. -/
theorem hasFiniteTargetZeroABCost_of_twoSidedSupport_nonempty
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (hA : T.supportA.Nonempty) (hB : T.supportB.Nonempty) :
    T.HasFiniteTargetZeroABCost P := by
  exact T.hasFiniteTargetZeroABCost_of_hasTargetZeroGoodBasePoint P
    (T.hasTargetZeroGoodBasePoint_of_twoSidedSupport_nonempty P hblocks hc hA hB)

/-- Realized-profile routing: in the two-sided support case, B1 already gives a
strict candidate through the B0 good-base point. -/
theorem hasStrictCandidate_of_hasFiniteTargetZeroABCost_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (h : T.HasFiniteTargetZeroABCost P) :
    T.HasStrictCandidate := by
  have hbase : T.HasGoodBasePoint P :=
    T.hasGoodBasePoint_of_hasFiniteTargetZeroABCost P h
  exact (T.hasStrictCandidate_iff_hasGoodBasePoint_of_profileRealizesCImage
    P hblocks hreal).2 hbase

/-- Two-sided support version of the realized-profile routing theorem. -/
theorem hasStrictCandidate_of_twoSidedSupport_nonempty_of_finiteTargetZeroABCost
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (hc : T.c ≠ 0)
    (hA : T.supportA.Nonempty) (hB : T.supportB.Nonempty) :
    T.HasStrictCandidate := by
  exact T.hasStrictCandidate_of_hasFiniteTargetZeroABCost_of_profileRealizesCImage
    P hblocks hreal
    (T.hasFiniteTargetZeroABCost_of_twoSidedSupport_nonempty P hblocks hc hA hB)

end ABCTriple
end ABD2
