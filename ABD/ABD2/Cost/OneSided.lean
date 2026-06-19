import ABD.ABD2.Cost.PureCLift

namespace ABD2
namespace ABCTriple

/-- C2b: full one-sided forced cost at a concrete bound.

This is the branch-sensitive quantitative predicate for the one-sided case.  It
records a nonzero scalar target `t`, an active one-sided good seed producing that
target, and a concrete C-lift realizing the same target, with the resulting full
lift small at bound `B`.

Unlike `PureForcedCLiftCostAtMost`, this remembers the seed and one-sided
structure, so it can route back to a small section. -/
def OneSidedForcedCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) : Prop :=
  ∃ seed : T.FullTangent,
  ∃ lift : T.FullTangent,
  ∃ t : ℤ,
    t ≠ 0 ∧
    T.OneSidedABSupport ∧
    T.GoodBasePoint P seed ∧
    T.HasCLift seed lift ∧
    T.abTarget seed = t ∧
    T.cLinearForm lift = t ∧
    T.SmallTangent lift B

/-- Existence of some finite full one-sided forced cost. -/
def HasFiniteOneSidedForcedCost
    (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  ∃ B : ℤ, T.OneSidedForcedCostAtMost P B

/-- A finite-cost B2 anatomy certificate induces the normalized C2b cost
predicate. -/
theorem oneSidedForcedCostAtMost_of_oneSidedForcedLiftCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.OneSidedForcedLiftCostAnatomy P B) :
    T.OneSidedForcedCostAtMost P B := by
  exact
    ⟨h.forced.seed, h.forced.lift, T.abTarget h.forced.seed,
      h.forced.target_ne_zero,
      h.forced.oneSided,
      h.forced.good,
      h.forced.cLift,
      rfl,
      h.forced.cLinearForm_eq_target,
      h.smallLift⟩

/-- Nonempty finite-cost B2 anatomy at a fixed bound gives C2b cost at that bound. -/
theorem oneSidedForcedCostAtMost_of_nonempty_oneSidedForcedLiftCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : Nonempty (T.OneSidedForcedLiftCostAnatomy P B)) :
    T.OneSidedForcedCostAtMost P B := by
  rcases h with ⟨hcert⟩
  exact T.oneSidedForcedCostAtMost_of_oneSidedForcedLiftCostAnatomy P hcert

/-- Finite B2 anatomy gives finite C2b forced one-sided cost. -/
theorem hasFiniteOneSidedForcedCost_of_hasFiniteOneSidedForcedLiftCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasFiniteOneSidedForcedLiftCostAnatomy P) :
    T.HasFiniteOneSidedForcedCost P := by
  rcases h with ⟨B, hB⟩
  exact ⟨B,
    T.oneSidedForcedCostAtMost_of_nonempty_oneSidedForcedLiftCostAnatomy P hB⟩

/-- A solved qualitative fibration in the one-sided support case gives finite
C2b forced one-sided cost. -/
theorem hasFiniteOneSidedForcedCost_of_qualitativeFibrationSolved
    (T : ABCTriple) (P : T.CImageProfile)
    (hside : T.OneSidedABSupport)
    (hqual : T.QualitativeFibrationSolved P) :
    T.HasFiniteOneSidedForcedCost P := by
  exact T.hasFiniteOneSidedForcedCost_of_hasFiniteOneSidedForcedLiftCostAnatomy P
    (T.hasFiniteOneSidedForcedLiftCostAnatomy_of_qualitativeFibrationSolved P hside hqual)

/-- C2b cost forgets to a pure C-lift cost at some nonzero scalar target. -/
theorem exists_nonzero_target_pureForcedCLiftCostAtMost_of_oneSidedForcedCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.OneSidedForcedCostAtMost P B) :
    ∃ t : ℤ, t ≠ 0 ∧ T.PureForcedCLiftCostAtMost t B := by
  rcases h with ⟨seed, lift, t, ht_ne, _hside, _hgood, _hlift,
    _htarget, hcLinear, hsmall⟩
  exact ⟨t, ht_ne, T.pureForcedCLiftCostAtMost_of_witness hcLinear hsmall⟩

/-- C2b cost routes back to a small section over a good base point. -/
theorem smallSectionExists_of_oneSidedForcedCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.OneSidedForcedCostAtMost P B) :
    T.SmallSectionExists P B := by
  rcases h with ⟨seed, lift, _t, _ht_ne, _hside, hgood, hclift,
    _htarget, _hcLinear, hsmall⟩
  refine ⟨seed, hgood, ?_⟩
  exact ⟨lift, hclift, hsmall⟩

/-- C2b cost gives a small strict candidate, via the existing small-section bridge. -/
theorem hasSmallStrictCandidate_of_oneSidedForcedCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.OneSidedForcedCostAtMost P B) :
    ∃ x : T.FullTangent, T.StrictCandidate x ∧ T.SmallTangent x B := by
  exact T.hasSmallStrictCandidate_of_smallSectionExists P
    (T.smallSectionExists_of_oneSidedForcedCostAtMost P h)

end ABCTriple
end ABD2
