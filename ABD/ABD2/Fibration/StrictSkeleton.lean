import ABD.ABD2.Fibration.Obstruction
import ABD.ABD2.Stratification.ValuationProfile
import ABD.ABD2.Reduction.RealizedProfile
import ABD.ABD2.Reduction.CImageGCDPositiveC

namespace ABD2
namespace ABCTriple

/-- Profile-level strict skeleton, expressed in the fibration language.

For any C-image profile which is actually realized by the C-side image, the
existence of a strict candidate is exactly the existence of a good point in the
AB-base.  This is the smallness-free SDC skeleton: the strict problem has been
moved to the base of the fibration. -/
theorem hasStrictCandidate_iff_hasGoodBasePoint_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P) :
    T.HasStrictCandidate ↔ T.HasGoodBasePoint P := by
  exact (T.hasStrictCandidate_iff_not_BadSeed_of_profileRealizesCImage
      P hblocks hreal).trans
    (T.hasGoodBasePoint_iff_not_BadSeed P).symm

/-- Profile-level strict skeleton, stated through the base obstruction. -/
theorem hasStrictCandidate_iff_not_BaseObstruction_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P) :
    T.HasStrictCandidate ↔ ¬ T.BaseObstruction P := by
  simpa [BaseObstruction] using
    (T.hasStrictCandidate_iff_not_BadSeed_of_profileRealizesCImage
      P hblocks hreal)

/-- Under a realized profile, the qualitative fibration condition is equivalent
only to the good-base condition: fiber nonemptiness follows from realization of
the C-image profile. -/
theorem qualitativeFibrationSolved_iff_hasGoodBasePoint_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P) :
    T.QualitativeFibrationSolved P ↔ T.HasGoodBasePoint P := by
  constructor
  · intro h
    exact h.1
  · intro hbase
    have hlift : T.HasCLiftForCompatibleSeeds P :=
      T.hasCLiftForCompatibleSeeds_of_profileRealizesCImage P hblocks hreal
    exact ⟨hbase,
      (T.fiberNonemptyForBase_iff_hasCLiftForCompatibleSeeds P).2 hlift⟩

/-- Smallness-free SDC skeleton as a qualitative fibration statement. -/
theorem hasStrictCandidate_iff_qualitativeFibrationSolved_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P) :
    T.HasStrictCandidate ↔ T.QualitativeFibrationSolved P := by
  exact (T.hasStrictCandidate_iff_hasGoodBasePoint_of_profileRealizesCImage
      P hblocks hreal).trans
    (T.qualitativeFibrationSolved_iff_hasGoodBasePoint_of_profileRealizesCImage
      P hblocks hreal).symm

/-- Same strict skeleton, using the stratification vocabulary. -/
theorem hasStrictCandidate_iff_hasGoodBasePoint_of_valuationProfileRealized
    (T : ABCTriple) (V : T.ValuationProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ValuationProfileRealized V) :
    T.HasStrictCandidate ↔ T.HasGoodBasePoint V := by
  exact T.hasStrictCandidate_iff_hasGoodBasePoint_of_profileRealizesCImage
    V hblocks hreal

/-- Same base-obstruction criterion, using the stratification vocabulary. -/
theorem hasStrictCandidate_iff_not_BaseObstruction_of_valuationProfileRealized
    (T : ABCTriple) (V : T.ValuationProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ValuationProfileRealized V) :
    T.HasStrictCandidate ↔ ¬ T.BaseObstruction V := by
  exact T.hasStrictCandidate_iff_not_BaseObstruction_of_profileRealizesCImage
    V hblocks hreal

/-- Same qualitative-fibration criterion, using the stratification vocabulary. -/
theorem hasStrictCandidate_iff_qualitativeFibrationSolved_of_valuationProfileRealized
    (T : ABCTriple) (V : T.ValuationProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ValuationProfileRealized V) :
    T.HasStrictCandidate ↔ T.QualitativeFibrationSolved V := by
  exact T.hasStrictCandidate_iff_qualitativeFibrationSolved_of_profileRealizesCImage
    V hblocks hreal

namespace RealizedCImageProfile

/-- A realized profile packages the strict skeleton as good-base existence. -/
theorem hasStrictCandidate_iff_hasGoodBasePoint
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.HasStrictCandidate ↔ T.HasGoodBasePoint R.profile := by
  exact T.hasStrictCandidate_iff_hasGoodBasePoint_of_profileRealizesCImage
    R.profile R.blocks R.realizes

/-- A realized profile packages the strict skeleton as failure of the base
obstruction. -/
theorem hasStrictCandidate_iff_not_BaseObstruction
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.HasStrictCandidate ↔ ¬ T.BaseObstruction R.profile := by
  exact T.hasStrictCandidate_iff_not_BaseObstruction_of_profileRealizesCImage
    R.profile R.blocks R.realizes

/-- A realized profile makes qualitative fibration equivalent to good-base
existence. -/
theorem qualitativeFibrationSolved_iff_hasGoodBasePoint
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.QualitativeFibrationSolved R.profile ↔ T.HasGoodBasePoint R.profile := by
  exact T.qualitativeFibrationSolved_iff_hasGoodBasePoint_of_profileRealizesCImage
    R.profile R.blocks R.realizes

/-- A realized profile packages the strict skeleton as qualitative fibration. -/
theorem hasStrictCandidate_iff_qualitativeFibrationSolved
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.HasStrictCandidate ↔ T.QualitativeFibrationSolved R.profile := by
  exact T.hasStrictCandidate_iff_qualitativeFibrationSolved_of_profileRealizesCImage
    R.profile R.blocks R.realizes

/-- Forward form: a good base point gives a strict candidate for a realized
profile. -/
theorem hasStrictCandidate_of_hasGoodBasePoint
    {T : ABCTriple} (R : T.RealizedCImageProfile)
    (hbase : T.HasGoodBasePoint R.profile) :
    T.HasStrictCandidate := by
  exact (R.hasStrictCandidate_iff_hasGoodBasePoint).2 hbase

/-- Reverse form: a strict candidate gives a good base point for a realized
profile. -/
theorem hasGoodBasePoint_of_hasStrictCandidate
    {T : ABCTriple} (R : T.RealizedCImageProfile)
    (hstrict : T.HasStrictCandidate) :
    T.HasGoodBasePoint R.profile := by
  exact (R.hasStrictCandidate_iff_hasGoodBasePoint).1 hstrict

end RealizedCImageProfile

/-- Canonical realized profile for the strict skeleton under the concrete
C-image gcd witness produced from `1 < c`. -/
def strictSkeletonRealizedProfile_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.RealizedCImageProfile where
  profile := (T.cImageGCDWitness_of_one_lt_c hblocks hc).profile
  blocks := hblocks
  realizes := T.profileRealizesCImage_of_one_lt_c hblocks hc

/-- Canonical smallness-free SDC skeleton: strict candidates are exactly good
base points over the concrete gcd profile. -/
theorem strictSkeleton_hasStrictCandidate_iff_hasGoodBasePoint_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.HasStrictCandidate ↔
      T.HasGoodBasePoint ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  simpa [strictSkeletonRealizedProfile_of_one_lt_c] using
    (T.strictSkeletonRealizedProfile_of_one_lt_c hblocks hc).hasStrictCandidate_iff_hasGoodBasePoint

/-- Canonical base-obstruction form of the strict skeleton. -/
theorem strictSkeleton_hasStrictCandidate_iff_not_BaseObstruction_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.HasStrictCandidate ↔
      ¬ T.BaseObstruction ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  simpa [strictSkeletonRealizedProfile_of_one_lt_c] using
    (T.strictSkeletonRealizedProfile_of_one_lt_c
       hblocks hc).hasStrictCandidate_iff_not_BaseObstruction

/-- Canonical qualitative-fibration form of the strict skeleton. -/
theorem strictSkeleton_hasStrictCandidate_iff_qualitativeFibrationSolved_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.HasStrictCandidate ↔
      T.QualitativeFibrationSolved
        ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  simpa [strictSkeletonRealizedProfile_of_one_lt_c] using
    (T.strictSkeletonRealizedProfile_of_one_lt_c
       hblocks hc).hasStrictCandidate_iff_qualitativeFibrationSolved

/-- Canonical good-base/qualitative-fibration equivalence. -/
theorem strictSkeleton_qualitativeFibrationSolved_iff_hasGoodBasePoint_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.QualitativeFibrationSolved
        ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) ↔
      T.HasGoodBasePoint ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  simpa [strictSkeletonRealizedProfile_of_one_lt_c] using
    (T.strictSkeletonRealizedProfile_of_one_lt_c
      hblocks hc).qualitativeFibrationSolved_iff_hasGoodBasePoint

end ABCTriple
end ABD2
