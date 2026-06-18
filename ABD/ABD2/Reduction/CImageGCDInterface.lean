import ABD.ABD2.Reduction.RealizedProfile

namespace ABD2
namespace ABCTriple

/-- Interface for the future concrete gcd theorem.

This does not yet compute the gcd.  It records exactly what the future
`cCoeffGCD` theorem must provide in ABD2: an integer gcd, a nonzero proof, and a
proof that the corresponding profile realizes the C-image. -/
structure CImageGCDWitness (T : ABCTriple) where
  gcd : ℤ
  gcd_ne_zero : gcd ≠ 0
  realizes : T.ProfileRealizesCImage
    { gcd := gcd
      gcd_ne_zero := gcd_ne_zero }

namespace CImageGCDWitness

/-- The C-image profile associated to a gcd witness. -/
def profile {T : ABCTriple} (W : T.CImageGCDWitness) : T.CImageProfile :=
  { gcd := W.gcd
    gcd_ne_zero := W.gcd_ne_zero }

/-- The witness realizes its associated profile. -/
theorem profile_realizes
    {T : ABCTriple} (W : T.CImageGCDWitness) :
    T.ProfileRealizesCImage W.profile := by
  simpa [profile] using W.realizes

/-- A gcd witness plus block decomposition packages into a realized profile. -/
def realizedProfile
    {T : ABCTriple} (W : T.CImageGCDWitness)
    (hblocks : T.SupportBlocksDecompose) :
    T.RealizedCImageProfile where
  profile := W.profile
  blocks := hblocks
  realizes := W.profile_realizes

/-- Gcd-witness form of the strict-candidate criterion. -/
theorem hasStrictCandidate_iff_not_BadSeed
    {T : ABCTriple} (W : T.CImageGCDWitness)
    (hblocks : T.SupportBlocksDecompose) :
    T.HasStrictCandidate ↔ ¬ T.BadSeed W.profile := by
  exact (W.realizedProfile hblocks).hasStrictCandidate_iff_not_BadSeed

/-- Gcd-witness form of the forward strict-candidate routing theorem. -/
theorem hasStrictCandidate_of_not_BadSeed
    {T : ABCTriple} (W : T.CImageGCDWitness)
    (hblocks : T.SupportBlocksDecompose)
    (hgood : ¬ T.BadSeed W.profile) :
    T.HasStrictCandidate := by
  exact ((W.hasStrictCandidate_iff_not_BadSeed hblocks).2 hgood)

/-- Gcd-witness form of the reverse strict-candidate obstruction theorem. -/
theorem not_BadSeed_of_hasStrictCandidate
    {T : ABCTriple} (W : T.CImageGCDWitness)
    (hblocks : T.SupportBlocksDecompose)
    (hstrict : T.HasStrictCandidate) :
    ¬ T.BadSeed W.profile := by
  exact ((W.hasStrictCandidate_iff_not_BadSeed hblocks).1 hstrict)

end CImageGCDWitness
end ABCTriple
end ABD2
