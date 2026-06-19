import ABD.ABD2.Gauge.CoordinateGauge

namespace ABD2
namespace ABCTriple

/-- A bound regime is a predicate on admissible bounds.

This keeps the final `abc`-level requirement abstract: later one can instantiate
it with `B < c^η`, `B = o(c)`, logarithmic bounds, conductor-style bounds, or any
other useful notion. -/
structure BoundRegime (T : ABCTriple) where
  accepts : ℤ → Prop

/-- A candidate whose gauge bound lies in a specified regime. -/
def HasGaugeCandidateInRegime
    (T : ABCTriple) (G : T.Gauge) (R : T.BoundRegime) : Prop :=
  ∃ B : ℤ, R.accepts B ∧ T.HasSmallStrictCandidateWith G B

/-- Register a candidate with an accepted bound as a regime-level candidate. -/
theorem hasGaugeCandidateInRegime_of_bound
    (T : ABCTriple) (G : T.Gauge) (R : T.BoundRegime) {B : ℤ}
    (hB : R.accepts B)
    (h : T.HasSmallStrictCandidateWith G B) :
    T.HasGaugeCandidateInRegime G R := by
  exact ⟨B, hB, h⟩

/-- A named alias for regimes intended to express power-saving or abc-level
smallness requirements. -/
abbrev PowerSavingRegime (T : ABCTriple) : Type :=
  T.BoundRegime

/-- Power-saving candidate, still abstract in the choice of final bound regime. -/
def HasPowerSavingCandidate
    (T : ABCTriple) (G : T.Gauge) (R : T.PowerSavingRegime) : Prop :=
  T.HasGaugeCandidateInRegime G R

end ABCTriple
end ABD2
