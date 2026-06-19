import ABD.ABD2.Cost.TwoSided
import ABD.ABD2.Fibration.OneSidedForcedLift

namespace ABD2
namespace ABCTriple

/-- C2a: pure forced C-lift preimage cost at a concrete scalar target.

This is the normalized scalar-target view of the C-side cost: the value `t` is
realized by the C-linear form on some full tangent whose coordinate size is
bounded by `B`.

For now this deliberately uses the existing full-tangent `SmallTangent` gauge,
because B2 already produces finite-cost lift certificates in that language.  A
later refinement can replace this by a C-mask-only gauge. -/
def PureForcedCLiftCostAtMost
    (T : ABCTriple) (t B : ℤ) : Prop :=
  BlockPreimageCostAtMost T.cLinearForm T.SmallTangent t B

/-- Existence of some finite pure forced C-lift cost for a fixed scalar target. -/
def HasFinitePureForcedCLiftCostAtTarget
    (T : ABCTriple) (t : ℤ) : Prop :=
  ∃ B : ℤ, T.PureForcedCLiftCostAtMost t B

/-- A concrete lift witness gives pure forced C-lift cost. -/
theorem pureForcedCLiftCostAtMost_of_witness
    (T : ABCTriple) {t B : ℤ} {lift : T.FullTangent}
    (hlinear : T.cLinearForm lift = t)
    (hsmall : T.SmallTangent lift B) :
    T.PureForcedCLiftCostAtMost t B := by
  exact blockPreimageCostAtMost_of_witness hlinear hsmall

/-- A pure forced C-lift cost predicate contains a lift witness. -/
theorem exists_lift_of_pureForcedCLiftCostAtMost
    (T : ABCTriple) {t B : ℤ}
    (h : T.PureForcedCLiftCostAtMost t B) :
    ∃ lift : T.FullTangent,
      T.cLinearForm lift = t ∧ T.SmallTangent lift B := by
  exact h

/-- A concrete pure forced C-lift cost bound gives finite pure cost. -/
theorem hasFinitePureForcedCLiftCostAtTarget_of_atMost
    (T : ABCTriple) {t B : ℤ}
    (h : T.PureForcedCLiftCostAtMost t B) :
    T.HasFinitePureForcedCLiftCostAtTarget t := by
  exact ⟨B, h⟩

/-- A finite-cost B2 anatomy certificate gives pure forced C-lift cost at its
forced nonzero target. -/
theorem pureForcedCLiftCostAtMost_of_oneSidedForcedLiftCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.OneSidedForcedLiftCostAnatomy P B) :
    T.PureForcedCLiftCostAtMost (T.abTarget h.forced.seed) B := by
  exact T.pureForcedCLiftCostAtMost_of_witness
    h.forced.cLinearForm_eq_target h.smallLift

/-- The scalar target supplied by a B2 finite-cost anatomy certificate is nonzero. -/
theorem target_ne_zero_of_oneSidedForcedLiftCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.OneSidedForcedLiftCostAnatomy P B) :
    T.abTarget h.forced.seed ≠ 0 := by
  exact h.forced.target_ne_zero

end ABCTriple
end ABD2
