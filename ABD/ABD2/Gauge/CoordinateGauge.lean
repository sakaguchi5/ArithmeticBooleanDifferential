import ABD.ABD2.Gauge.Gauge
import ABD.ABD2.Reduction.SmallLiftData

namespace ABD2
namespace ABCTriple

/-- The existing ABD2 coordinatewise bound as a gauge. -/
def coordinateGauge (T : ABCTriple) : T.Gauge where
  small := fun x B => T.SmallTangent x B

@[simp]
theorem coordinateGauge_small_iff
    (T : ABCTriple) (x : T.FullTangent) (B : ℤ) :
    T.coordinateGauge.small x B ↔ T.SmallTangent x B := by
  rfl

/-- Existing small block-lift data produces a small strict candidate in the
coordinate gauge. -/
theorem hasSmallStrictCandidateWith_coordinateGauge_of_smallBlockLiftData
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.SmallBlockLiftData P B) :
    T.HasSmallStrictCandidateWith T.coordinateGauge B := by
  simpa [HasSmallStrictCandidateWith, coordinateGauge] using
    T.hasSmallStrictCandidate_of_smallBlockLiftData P h

end ABCTriple
end ABD2
