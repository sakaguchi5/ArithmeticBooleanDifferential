import ABD.ABD2.Fibration.BadSeedInclusion

namespace ABD2
namespace ABCTriple

/-- Phase 4 qualitative form: for a realized C-image profile, solving the
qualitative fibration problem is exactly avoiding the first bad-seed pattern. -/
theorem qualitativeFibrationSolved_iff_not_BadSeed_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P) :
    T.QualitativeFibrationSolved P ↔ ¬ T.BadSeed P := by
  exact (T.qualitativeFibrationSolved_iff_hasGoodBasePoint_of_profileRealizesCImage
      P hblocks hreal).trans
    (T.hasGoodBasePoint_iff_not_BadSeed P)

/-- Phase 4 qualitative form through the fibration-language base obstruction. -/
theorem qualitativeFibrationSolved_iff_not_BaseObstruction_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P) :
    T.QualitativeFibrationSolved P ↔ ¬ T.BaseObstruction P := by
  exact (T.qualitativeFibrationSolved_iff_hasGoodBasePoint_of_profileRealizesCImage
      P hblocks hreal).trans
    (T.not_baseObstruction_iff_hasGoodBasePoint P).symm

/-- Phase 4 qualitative form as failure of the AB-base inclusion into the
Wronskian-degenerate locus. -/
theorem qualitativeFibrationSolved_iff_not_ABBase_le_BaseWronskianKernel_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P) :
    T.QualitativeFibrationSolved P ↔
      ¬ (T.ABBase P ≤ T.BaseWronskianKernel) := by
  exact (T.qualitativeFibrationSolved_iff_hasGoodBasePoint_of_profileRealizesCImage
      P hblocks hreal).trans
    (T.hasGoodBasePoint_iff_not_ABBase_le_BaseWronskianKernel P)

/-- Forward routing: once a realized profile is fixed, absence of the bad seed
solves the qualitative fibration problem. -/
theorem qualitativeFibrationSolved_of_not_BadSeed_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (hgood : ¬ T.BadSeed P) :
    T.QualitativeFibrationSolved P := by
  exact (T.qualitativeFibrationSolved_iff_not_BadSeed_of_profileRealizesCImage
    P hblocks hreal).2 hgood

/-- Reverse obstruction extraction: a solved qualitative fibration rules out the
first bad-seed pattern. -/
theorem not_BadSeed_of_qualitativeFibrationSolved_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (hqual : T.QualitativeFibrationSolved P) :
    ¬ T.BadSeed P := by
  exact (T.qualitativeFibrationSolved_iff_not_BadSeed_of_profileRealizesCImage
    P hblocks hreal).1 hqual

/-- Forward routing from strict candidates to qualitative fibration, for a
realized profile.  Together with the already existing converse, this completes
Phase 4's qualitative equivalence. -/
theorem qualitativeFibrationSolved_of_hasStrictCandidate_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (hstrict : T.HasStrictCandidate) :
    T.QualitativeFibrationSolved P := by
  exact (T.hasStrictCandidate_iff_qualitativeFibrationSolved_of_profileRealizesCImage
    P hblocks hreal).1 hstrict

/-- Converse routing from qualitative fibration to strict candidates, stated at
realized-profile level. -/
theorem hasStrictCandidate_of_qualitativeFibrationSolved_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (hqual : T.QualitativeFibrationSolved P) :
    T.HasStrictCandidate := by
  exact (T.hasStrictCandidate_iff_qualitativeFibrationSolved_of_profileRealizesCImage
    P hblocks hreal).2 hqual

namespace RealizedCImageProfile

/-- A realized profile makes qualitative fibration equivalent to avoiding the
first bad-seed pattern. -/
theorem qualitativeFibrationSolved_iff_not_BadSeed
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.QualitativeFibrationSolved R.profile ↔ ¬ T.BadSeed R.profile := by
  exact T.qualitativeFibrationSolved_iff_not_BadSeed_of_profileRealizesCImage
    R.profile R.blocks R.realizes

/-- A realized profile makes qualitative fibration equivalent to failure of the
base obstruction. -/
theorem qualitativeFibrationSolved_iff_not_BaseObstruction
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.QualitativeFibrationSolved R.profile ↔ ¬ T.BaseObstruction R.profile := by
  exact T.qualitativeFibrationSolved_iff_not_BaseObstruction_of_profileRealizesCImage
    R.profile R.blocks R.realizes

/-- A realized profile makes qualitative fibration equivalent to failure of the
AB-base inclusion into the Wronskian-degenerate locus. -/
theorem qualitativeFibrationSolved_iff_not_ABBase_le_BaseWronskianKernel
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.QualitativeFibrationSolved R.profile ↔
      ¬ (T.ABBase R.profile ≤ T.BaseWronskianKernel) := by
  exact T.qualitativeFibrationSolved_iff_not_ABBase_le_BaseWronskianKernel_of_profileRealizesCImage
    R.profile R.blocks R.realizes

/-- Forward form: avoiding the first bad-seed pattern solves the qualitative
fibration for a realized profile. -/
theorem qualitativeFibrationSolved_of_not_BadSeed
    {T : ABCTriple} (R : T.RealizedCImageProfile)
    (hgood : ¬ T.BadSeed R.profile) :
    T.QualitativeFibrationSolved R.profile := by
  exact (R.qualitativeFibrationSolved_iff_not_BadSeed).2 hgood

/-- Reverse form: qualitative fibration excludes the first bad-seed pattern. -/
theorem not_BadSeed_of_qualitativeFibrationSolved
    {T : ABCTriple} (R : T.RealizedCImageProfile)
    (hqual : T.QualitativeFibrationSolved R.profile) :
    ¬ T.BadSeed R.profile := by
  exact (R.qualitativeFibrationSolved_iff_not_BadSeed).1 hqual

end RealizedCImageProfile

/-- Canonical qualitative criterion under `1 < c`: the qualitative fibration is
solved exactly when the concrete gcd profile avoids the first bad-seed pattern. -/
theorem qualitativeFibrationSolved_iff_not_BadSeed_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.QualitativeFibrationSolved
        ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) ↔
      ¬ T.BadSeed ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  exact T.qualitativeFibrationSolved_iff_not_BadSeed_of_profileRealizesCImage
    ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile)
    hblocks (T.profileRealizesCImage_of_one_lt_c hblocks hc)

/-- Canonical base-obstruction form under `1 < c`. -/
theorem qualitativeFibrationSolved_iff_not_BaseObstruction_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.QualitativeFibrationSolved
        ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) ↔
      ¬ T.BaseObstruction ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  exact T.qualitativeFibrationSolved_iff_not_BaseObstruction_of_profileRealizesCImage
    ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile)
    hblocks (T.profileRealizesCImage_of_one_lt_c hblocks hc)

/-- Canonical inclusion form under `1 < c`. -/
theorem qualitativeFibrationSolved_iff_not_ABBase_le_BaseWronskianKernel_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.QualitativeFibrationSolved
        ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) ↔
      ¬ (T.ABBase ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) ≤
        T.BaseWronskianKernel) := by
  exact T.qualitativeFibrationSolved_iff_not_ABBase_le_BaseWronskianKernel_of_profileRealizesCImage
    ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile)
    hblocks (T.profileRealizesCImage_of_one_lt_c hblocks hc)

/-- Canonical equivalence, oriented from qualitative fibration to strict
candidates. -/
theorem qualitativeFibrationSolved_iff_hasStrictCandidate_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.QualitativeFibrationSolved
        ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) ↔
      T.HasStrictCandidate := by
  exact (T.strictSkeleton_hasStrictCandidate_iff_qualitativeFibrationSolved_of_one_lt_c
    hblocks hc).symm

end ABCTriple
end ABD2
