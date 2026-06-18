import ABD.ABD2.Reduction.CImageToLift

namespace ABD2
namespace ABCTriple

/-- A realized C-image profile turns failure of `BadSeed` into a strict candidate.

This is the abstract ABD2 composite strengthening corresponding to the old
Theorem 1--3 combination, but stated as a one-way routing theorem. -/
theorem hasStrictCandidate_of_not_BadSeed_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (hgood : ¬ T.BadSeed P) :
    T.HasStrictCandidate := by
  have hliftAll : T.HasCLiftForCompatibleSeeds P :=
    T.hasCLiftForCompatibleSeeds_of_profileRealizesCImage P hblocks hreal
  have hseed : T.HasGoodABSeed P :=
    (T.hasGoodABSeed_iff_not_BadSeed P).2 hgood
  exact T.hasStrictCandidate_of_nonzero_compatible_seed P hliftAll hseed

end ABCTriple
end ABD2
