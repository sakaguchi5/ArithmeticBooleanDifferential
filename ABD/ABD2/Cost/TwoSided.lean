import ABD.ABD2.Cost.Aggregate
import ABD.ABD2.Fibration.TargetZeroCostAnatomy

namespace ABD2
namespace ABCTriple

/-- C1: two-sided AB-cancellation cost at a concrete bound.

This is the first quantitative-cost predicate for the two-sided branch.  It
records that a nonzero scalar `t` is realized on the A side while the A/B
values cancel internally, and that the AB part of the full tangent is small at
bound `B`.

The definition deliberately stays on `FullTangent`, because B1 already provides
`TargetZeroABCostAnatomy` in that language.  Later files can refine this to
separate A- and B-block preimage costs. -/
def TwoSidedABCancellationCostAtMost
    (T : ABCTriple) (B : ℤ) : Prop :=
  ∃ x : T.FullTangent,
  ∃ t : ℤ,
    t ≠ 0 ∧
    T.ADerivValue x = t ∧
    T.ADerivValue x + T.BDerivValue x = 0 ∧
    T.ABSmallTangent x B

/-- Existence of some finite two-sided AB-cancellation bound. -/
def HasFiniteTwoSidedABCancellationCost
    (T : ABCTriple) : Prop :=
  ∃ B : ℤ, T.TwoSidedABCancellationCostAtMost B

/-- In a completed B1 anatomy certificate, the A-value is nonzero.

If the A-value were zero, the cancellation field would force the B-value to be
zero as well, making the Wronskian vanish, contradicting the certificate. -/
theorem aValue_ne_zero_of_targetZeroABCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.TargetZeroABCostAnatomy P B) :
    h.aValue ≠ 0 := by
  intro ha0
  have hA0 : formalDeriv T.support h.point T.a = 0 := by
    simpa [ABCTriple.ADerivValue, ha0] using h.aValue_eq
  have hb0 : h.bValue = 0 := by
    simpa [ha0] using h.cancellation
  have hB0 : formalDeriv T.support h.point T.b = 0 := by
    simpa [ABCTriple.BDerivValue, hb0] using h.bValue_eq
  have hW0 : T.Wronskian h.point = 0 := by
    unfold ABCTriple.Wronskian
    simp [hA0, hB0]
  exact h.wronskian_ne_zero hW0

/-- The B1 anatomy certificate induces the normalized C1 cost predicate. -/
theorem twoSidedABCancellationCostAtMost_of_targetZeroABCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.TargetZeroABCostAnatomy P B) :
    T.TwoSidedABCancellationCostAtMost B := by
  have hcancelD : T.ADerivValue h.point + T.BDerivValue h.point = 0 := by
    rw [h.aValue_eq, h.bValue_eq]
    exact h.cancellation
  exact
    ⟨h.point, h.aValue,
      T.aValue_ne_zero_of_targetZeroABCostAnatomy P h,
      h.aValue_eq,
      hcancelD,
      h.abSmall⟩

/-- Nonempty B1 anatomy at a fixed bound gives C1 cost at the same bound. -/
theorem twoSidedABCancellationCostAtMost_of_nonempty_targetZeroABCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : Nonempty (T.TargetZeroABCostAnatomy P B)) :
    T.TwoSidedABCancellationCostAtMost B := by
  rcases h with ⟨hcert⟩
  exact T.twoSidedABCancellationCostAtMost_of_targetZeroABCostAnatomy P hcert

/-- Finite B1 anatomy gives finite two-sided AB-cancellation cost. -/
theorem hasFiniteTwoSidedABCancellationCost_of_hasFiniteTargetZeroABCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasFiniteTargetZeroABCostAnatomy P) :
    T.HasFiniteTwoSidedABCancellationCost := by
  rcases h with ⟨B, hB⟩
  exact ⟨B,
    T.twoSidedABCancellationCostAtMost_of_nonempty_targetZeroABCostAnatomy P hB⟩

/-- Two-sided support gives finite C1 cost, by routing through the completed B1
anatomy object. -/
theorem hasFiniteTwoSidedABCancellationCost_of_twoSidedSupport_nonempty
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (hA : T.supportA.Nonempty) (hB : T.supportB.Nonempty) :
    T.HasFiniteTwoSidedABCancellationCost := by
  exact T.hasFiniteTwoSidedABCancellationCost_of_hasFiniteTargetZeroABCostAnatomy P
    (T.hasFiniteTargetZeroABCostAnatomy_of_twoSidedSupport_nonempty P hblocks hc hA hB)

end ABCTriple
end ABD2
