import ABD.ABD2.Reduction.StrictIffFromProfile
import ABD.ABD2.Reduction.SmallBlockLift

namespace ABD2
namespace ABCTriple

/-- A realized C-image profile packages together the support decomposition and the
fact that a profile describes the C-image.

The arithmetic `cCoeffGCD` theorem should eventually produce one of these
packages.  Once this package exists, strict-candidate routing no longer needs to
look at the arithmetic proof. -/
structure RealizedCImageProfile (T : ABCTriple) where
  profile : T.CImageProfile
  blocks : T.SupportBlocksDecompose
  realizes : T.ProfileRealizesCImage profile

namespace RealizedCImageProfile

/-- A realized profile gives C-lifts for every compatible seed. -/
theorem hasCLiftForCompatibleSeeds
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.HasCLiftForCompatibleSeeds R.profile := by
  exact T.hasCLiftForCompatibleSeeds_of_profileRealizesCImage
    R.profile R.blocks R.realizes

/-- A realized profile turns the seed-level bad pattern into the exact obstruction
to strict candidates. -/
theorem hasStrictCandidate_iff_not_BadSeed
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.HasStrictCandidate ↔ ¬ T.BadSeed R.profile := by
  exact T.hasStrictCandidate_iff_not_BadSeed_of_profileRealizesCImage
    R.profile R.blocks R.realizes

/-- Forward direction of the realized-profile strict-candidate criterion. -/
theorem hasStrictCandidate_of_not_BadSeed
    {T : ABCTriple} (R : T.RealizedCImageProfile)
    (hgood : ¬ T.BadSeed R.profile) :
    T.HasStrictCandidate := by
  exact (R.hasStrictCandidate_iff_not_BadSeed).2 hgood

/-- Reverse direction of the realized-profile strict-candidate criterion. -/
theorem not_BadSeed_of_hasStrictCandidate
    {T : ABCTriple} (R : T.RealizedCImageProfile)
    (hstrict : T.HasStrictCandidate) :
    ¬ T.BadSeed R.profile := by
  exact (R.hasStrictCandidate_iff_not_BadSeed).1 hstrict

/-- If a realized profile has a small block lift, then it has a small strict
candidate.  This is just the existing small routing theorem with the profile
package as the input object. -/
theorem hasSmallStrictCandidate_of_hasSmallBlockLift
    {T : ABCTriple} (R : T.RealizedCImageProfile) {B : ℤ}
    (h : T.HasSmallBlockLift R.profile B) :
    ∃ x : T.FullTangent, T.StrictCandidate x ∧ T.SmallTangent x B := by
  exact T.hasSmallStrictCandidate_of_hasSmallBlockLift R.profile h

end RealizedCImageProfile
end ABCTriple
end ABD2
