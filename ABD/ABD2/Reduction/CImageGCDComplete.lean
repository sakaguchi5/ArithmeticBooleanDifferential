import ABD.ABD2.Reduction.CImageGCDNonzero

namespace ABD2
namespace ABCTriple

/-- Final concrete C-image gcd witness, using the natural nonzero-coefficient
hypothesis instead of an explicit `gcd ≠ 0` proof. -/
def cImageGCDWitness_of_exists_nonzero_cCoeffOnC
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hnonzero : ∃ p : {p : ℕ // p ∈ T.supportC}, T.cCoeffOnC p ≠ 0) :
    T.CImageGCDWitness :=
  T.cImageGCDWitness_cCoeffFullGCD hblocks
    (T.cCoeffFullGCD_ne_zero_of_exists_nonzero_cCoeffOnC hnonzero)

/-- Full-support variant of the final concrete witness. -/
def cImageGCDWitness_of_exists_nonzero_fullCoeff
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hnonzero : ∃ p : {p : ℕ // p ∈ T.support}, T.cCoeffOnFullSupport p ≠ 0) :
    T.CImageGCDWitness :=
  T.cImageGCDWitness_cCoeffFullGCD hblocks
    (T.cCoeffFullGCD_ne_zero_of_exists_nonzero_fullCoeff hnonzero)

/-- Realization theorem with a C-support nonzero coefficient hypothesis. -/
theorem profileRealizesCImage_of_exists_nonzero_cCoeffOnC
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hnonzero : ∃ p : {p : ℕ // p ∈ T.supportC}, T.cCoeffOnC p ≠ 0) :
    T.ProfileRealizesCImage
      ((T.cImageGCDWitness_of_exists_nonzero_cCoeffOnC hblocks hnonzero).profile) := by
  exact (T.cImageGCDWitness_of_exists_nonzero_cCoeffOnC
    hblocks hnonzero).profile_realizes

/-- Final Step-D strict-candidate criterion using the C-support nonzero coefficient
hypothesis. -/
theorem hasStrictCandidate_iff_not_BadSeed_of_exists_nonzero_cCoeffOnC
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hnonzero : ∃ p : {p : ℕ // p ∈ T.supportC}, T.cCoeffOnC p ≠ 0) :
    T.HasStrictCandidate ↔
      ¬ T.BadSeed
        ((T.cImageGCDWitness_of_exists_nonzero_cCoeffOnC hblocks hnonzero).profile) := by
  let W := T.cImageGCDWitness_of_exists_nonzero_cCoeffOnC hblocks hnonzero
  exact W.hasStrictCandidate_iff_not_BadSeed hblocks

/-- Forward routing form of the final Step-D criterion. -/
theorem hasStrictCandidate_of_not_BadSeed_of_exists_nonzero_cCoeffOnC
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hnonzero : ∃ p : {p : ℕ // p ∈ T.supportC}, T.cCoeffOnC p ≠ 0)
    (hgood :
      ¬ T.BadSeed
        ((T.cImageGCDWitness_of_exists_nonzero_cCoeffOnC hblocks hnonzero).profile)) :
    T.HasStrictCandidate := by
  exact ((T.hasStrictCandidate_iff_not_BadSeed_of_exists_nonzero_cCoeffOnC
    hblocks hnonzero).2 hgood)

/-- Reverse obstruction form of the final Step-D criterion. -/
theorem not_BadSeed_of_hasStrictCandidate_of_exists_nonzero_cCoeffOnC
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hnonzero : ∃ p : {p : ℕ // p ∈ T.supportC}, T.cCoeffOnC p ≠ 0)
    (hstrict : T.HasStrictCandidate) :
    ¬ T.BadSeed
      ((T.cImageGCDWitness_of_exists_nonzero_cCoeffOnC hblocks hnonzero).profile) := by
  exact ((T.hasStrictCandidate_iff_not_BadSeed_of_exists_nonzero_cCoeffOnC
    hblocks hnonzero).1 hstrict)

/-- Full-support variant of the final Step-D strict-candidate criterion. -/
theorem hasStrictCandidate_iff_not_BadSeed_of_exists_nonzero_fullCoeff
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hnonzero : ∃ p : {p : ℕ // p ∈ T.support}, T.cCoeffOnFullSupport p ≠ 0) :
    T.HasStrictCandidate ↔
      ¬ T.BadSeed
        ((T.cImageGCDWitness_of_exists_nonzero_fullCoeff hblocks hnonzero).profile) := by
  let W := T.cImageGCDWitness_of_exists_nonzero_fullCoeff hblocks hnonzero
  exact W.hasStrictCandidate_iff_not_BadSeed hblocks

end ABCTriple
end ABD2
