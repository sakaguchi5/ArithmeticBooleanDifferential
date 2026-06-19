import ABD.ABD2.Cost.OneSided
import ABD.ABD2.Gauge.CoordinateGauge

namespace ABD2
namespace ABCTriple

/-- C3 bridge: C2b one-sided forced cost gives a coordinate-gauge small strict
candidate.

This is the first bridge from the branch-sensitive cost layer back into the
existing gauge layer.  It uses the existing `SmallTangent` bound carried by
`OneSidedForcedCostAtMost`, interpreted as the coordinate gauge. -/
theorem hasSmallStrictCandidateWith_coordinateGauge_of_oneSidedForcedCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.OneSidedForcedCostAtMost P B) :
    T.HasSmallStrictCandidateWith T.coordinateGauge B := by
  rcases T.hasSmallStrictCandidate_of_oneSidedForcedCostAtMost P h with
    ⟨x, hxstrict, hxsmall⟩
  exact ⟨x, hxstrict, hxsmall⟩

/-- A finite-cost B2 anatomy certificate also gives a coordinate-gauge small
strict candidate at the same bound. -/
theorem hasSmallStrictCandidateWith_coordinateGauge_of_oneSidedForcedLiftCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.OneSidedForcedLiftCostAnatomy P B) :
    T.HasSmallStrictCandidateWith T.coordinateGauge B := by
  exact T.hasSmallStrictCandidateWith_coordinateGauge_of_oneSidedForcedCostAtMost P
    (T.oneSidedForcedCostAtMost_of_oneSidedForcedLiftCostAnatomy P h)

/-- Nonempty one-sided finite-cost anatomy at a fixed bound gives a
coordinate-gauge small strict candidate at that bound. -/
theorem hasSmallStrictCandidateWith_coordinateGauge_of_nonempty_oneSidedForcedLiftCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : Nonempty (T.OneSidedForcedLiftCostAnatomy P B)) :
    T.HasSmallStrictCandidateWith T.coordinateGauge B := by
  rcases h with ⟨hcert⟩
  exact T.hasSmallStrictCandidateWith_coordinateGauge_of_oneSidedForcedLiftCostAnatomy P hcert

end ABCTriple
end ABD2
