import ABD.ABD2.Reduction.StrictReduction

namespace ABD2
namespace ABCTriple

/-- A gauge is an abstract smallness predicate on full tangents.

The coordinate bound used by ABD2 is one gauge, but this interface allows later
height, logarithmic, support-sensitive, or power-saving gauges to be compared
without changing the fibration layer. -/
structure Gauge (T : ABCTriple) where
  small : T.FullTangent → ℤ → Prop

/-- A strict candidate satisfying a chosen gauge bound. -/
def HasSmallStrictCandidateWith
    (T : ABCTriple) (G : T.Gauge) (B : ℤ) : Prop :=
  ∃ x : T.FullTangent, T.StrictCandidate x ∧ G.small x B

/-- Gauge comparison: every `G`-small point is also `H`-small. -/
def GaugeDominates (T : ABCTriple) (G H : T.Gauge) : Prop :=
  ∀ x : T.FullTangent, ∀ B : ℤ, G.small x B → H.small x B

/-- Move a small strict candidate along a gauge comparison. -/
theorem hasSmallStrictCandidateWith_of_gaugeDominates
    (T : ABCTriple) {G H : T.Gauge} {B : ℤ}
    (hdom : T.GaugeDominates G H)
    (h : T.HasSmallStrictCandidateWith G B) :
    T.HasSmallStrictCandidateWith H B := by
  rcases h with ⟨x, hxstrict, hxsmall⟩
  exact ⟨x, hxstrict, hdom x B hxsmall⟩

end ABCTriple
end ABD2
