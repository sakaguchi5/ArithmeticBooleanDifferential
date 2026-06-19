import ABD.ABD2.Fibration.TargetZeroCost

namespace ABD2
namespace ABCTriple

/-- The A-side derivative value carried by a full tangent.

B1 uses this only as bookkeeping: after B0 has made the C-target vanish, the
remaining cost to watch is how the A/B derivative values cancel inside the AB
part. -/
def ADerivValue (T : ABCTriple) (x : T.FullTangent) : ℤ :=
  formalDeriv T.support x T.a

/-- The B-side derivative value carried by a full tangent. -/
def BDerivValue (T : ABCTriple) (x : T.FullTangent) : ℤ :=
  formalDeriv T.support x T.b

/-- The AB target is the sum of the A- and B-derivative values. -/
theorem abTarget_eq_ADerivValue_add_BDerivValue
    (T : ABCTriple) (x : T.FullTangent) :
    T.abTarget x = T.ADerivValue x + T.BDerivValue x := by
  unfold ABCTriple.abTarget ABCTriple.ADerivValue ABCTriple.BDerivValue
  rw [T.formalDeriv_a_eq_maskA x]
  rw [T.formalDeriv_b_eq_maskB x]

/-- A target-zero good base point has internally cancelling AB derivative values. -/
theorem ADerivValue_add_BDerivValue_eq_zero_of_targetZeroGoodBasePoint
    (T : ABCTriple) (P : T.CImageProfile) {x : T.FullTangent}
    (h : T.TargetZeroGoodBasePoint P x) :
    T.ADerivValue x + T.BDerivValue x = 0 := by
  rw [← T.abTarget_eq_ADerivValue_add_BDerivValue x]
  exact h.2

/-- A bounded target-zero point has internally cancelling AB derivative values. -/
theorem ADerivValue_add_BDerivValue_eq_zero_of_targetZeroGoodBasePointAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ} {x : T.FullTangent}
    (hzero : T.TargetZeroGoodBasePoint P x)
    (_hsmall : T.ABSmallTangent x B) :
    T.ADerivValue x + T.BDerivValue x = 0 := by
  exact T.ADerivValue_add_BDerivValue_eq_zero_of_targetZeroGoodBasePoint P hzero

/-- A target-zero good base point is Wronskian-nondegenerate. -/
theorem wronskian_ne_zero_of_targetZeroGoodBasePoint
    (T : ABCTriple) (P : T.CImageProfile) {x : T.FullTangent}
    (h : T.TargetZeroGoodBasePoint P x) :
    T.Wronskian x ≠ 0 := by
  exact (T.targetZeroGoodBasePoint_iff P x).1 h |>.2.1

/-- A concrete B1 certificate.

This is the completed B1 bookkeeping object.  It records not only that a
`TargetZeroGoodBasePoint` exists below an AB coordinate bound, but also the
A/B derivative values whose sum is zero.  Thus the cost is explicitly attached
to AB cancellation rather than to a C-lift. -/
structure TargetZeroABCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) where
  point : T.FullTangent
  targetZero : T.TargetZeroGoodBasePoint P point
  abSmall : T.ABSmallTangent point B
  aValue : ℤ
  bValue : ℤ
  aValue_eq : T.ADerivValue point = aValue
  bValue_eq : T.BDerivValue point = bValue
  cancellation : aValue + bValue = 0
  wronskian_ne_zero : T.Wronskian point ≠ 0

/-- Forget the derivative bookkeeping from a B1 anatomy certificate. -/
theorem targetZeroGoodBasePointAtMost_of_targetZeroABCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.TargetZeroABCostAnatomy P B) :
    T.TargetZeroGoodBasePointAtMost P B := by
  exact ⟨h.point, h.targetZero, h.abSmall⟩

/-- Build the existence of a B1 anatomy certificate from the bounded target-zero
object.

This is the Prop-level constructor.  It avoids extracting data from a `Prop`
into `Type`; it only proves that such data is nonempty. -/
theorem nonempty_targetZeroABCostAnatomy_of_targetZeroGoodBasePointAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.TargetZeroGoodBasePointAtMost P B) :
    Nonempty (T.TargetZeroABCostAnatomy P B) := by
  rcases h with ⟨x, hzero, hsmall⟩
  have hcancel : T.ADerivValue x + T.BDerivValue x = 0 :=
    T.ADerivValue_add_BDerivValue_eq_zero_of_targetZeroGoodBasePoint P hzero
  have hW : T.Wronskian x ≠ 0 :=
    T.wronskian_ne_zero_of_targetZeroGoodBasePoint P hzero
  refine ⟨?_⟩
  exact
    { point := x
      targetZero := hzero
      abSmall := hsmall
      aValue := T.ADerivValue x
      bValue := T.BDerivValue x
      aValue_eq := rfl
      bValue_eq := rfl
      cancellation := hcancel
      wronskian_ne_zero := hW }

/-- Choose one B1 anatomy certificate from the bounded target-zero object.

This is only a chosen representative, obtained by classical choice.  Prefer the
`Nonempty` theorem for Prop-level routing. -/
noncomputable def targetZeroABCostAnatomy_of_targetZeroGoodBasePointAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.TargetZeroGoodBasePointAtMost P B) :
    T.TargetZeroABCostAnatomy P B :=
  Classical.choice
    (T.nonempty_targetZeroABCostAnatomy_of_targetZeroGoodBasePointAtMost P h)

/-- Bounded target-zero AB cost is equivalent to the existence of the completed
anatomy certificate. -/
theorem nonempty_targetZeroABCostAnatomy_iff_targetZeroGoodBasePointAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ} :
    Nonempty (T.TargetZeroABCostAnatomy P B) ↔
      T.TargetZeroGoodBasePointAtMost P B := by
  constructor
  · intro h
    rcases h with ⟨hcert⟩
    exact T.targetZeroGoodBasePointAtMost_of_targetZeroABCostAnatomy P hcert
  · intro h
    exact T.nonempty_targetZeroABCostAnatomy_of_targetZeroGoodBasePointAtMost P h

/-- Existence of a completed finite B1 anatomy certificate. -/
def HasFiniteTargetZeroABCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  ∃ B : ℤ, Nonempty (T.TargetZeroABCostAnatomy P B)

/-- Finite B1 cost and finite B1 anatomy are equivalent. -/
theorem hasFiniteTargetZeroABCostAnatomy_iff_hasFiniteTargetZeroABCost
    (T : ABCTriple) (P : T.CImageProfile) :
    T.HasFiniteTargetZeroABCostAnatomy P ↔ T.HasFiniteTargetZeroABCost P := by
  constructor
  · intro h
    rcases h with ⟨B, hB⟩
    exact ⟨B,
      (T.nonempty_targetZeroABCostAnatomy_iff_targetZeroGoodBasePointAtMost P).1 hB⟩
  · intro h
    rcases h with ⟨B, hB⟩
    exact ⟨B,
      (T.nonempty_targetZeroABCostAnatomy_iff_targetZeroGoodBasePointAtMost P).2 hB⟩

/-- A completed B1 certificate still gives the B0 target-zero object. -/
theorem hasTargetZeroGoodBasePoint_of_hasFiniteTargetZeroABCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasFiniteTargetZeroABCostAnatomy P) :
    T.HasTargetZeroGoodBasePoint P := by
  have hcost : T.HasFiniteTargetZeroABCost P :=
    (T.hasFiniteTargetZeroABCostAnatomy_iff_hasFiniteTargetZeroABCost P).1 h
  exact T.hasTargetZeroGoodBasePoint_of_hasFiniteTargetZeroABCost P hcost

/-- B1 completed theorem: two-sided support gives a finite AB-cancellation anatomy
certificate.

This is still not a power-saving theorem.  It says that after B0, the remaining
finite cost can be represented as AB-side cancellation data: an AB-small
bounded point whose A/B derivative values cancel and whose Wronskian remains
nonzero. -/
theorem hasFiniteTargetZeroABCostAnatomy_of_twoSidedSupport_nonempty
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (hA : T.supportA.Nonempty) (hB : T.supportB.Nonempty) :
    T.HasFiniteTargetZeroABCostAnatomy P := by
  exact (T.hasFiniteTargetZeroABCostAnatomy_iff_hasFiniteTargetZeroABCost P).2
    (T.hasFiniteTargetZeroABCost_of_twoSidedSupport_nonempty P hblocks hc hA hB)

/-- Realized-profile routing from the completed B1 anatomy certificate. -/
theorem hasStrictCandidate_of_hasFiniteTargetZeroABCostAnatomy_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (h : T.HasFiniteTargetZeroABCostAnatomy P) :
    T.HasStrictCandidate := by
  exact T.hasStrictCandidate_of_hasFiniteTargetZeroABCost_of_profileRealizesCImage
    P hblocks hreal
    ((T.hasFiniteTargetZeroABCostAnatomy_iff_hasFiniteTargetZeroABCost P).1 h)

/-- Two-sided support version of the realized-profile routing theorem, using the
completed B1 anatomy object. -/
theorem hasStrictCandidate_of_twoSidedSupport_nonempty_of_targetZeroABCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (hc : T.c ≠ 0)
    (hA : T.supportA.Nonempty) (hB : T.supportB.Nonempty) :
    T.HasStrictCandidate := by
  exact T.hasStrictCandidate_of_hasFiniteTargetZeroABCostAnatomy_of_profileRealizesCImage
    P hblocks hreal
    (T.hasFiniteTargetZeroABCostAnatomy_of_twoSidedSupport_nonempty P hblocks hc hA hB)

end ABCTriple
end ABD2
