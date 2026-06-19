import ABD.ABD2.Fibration.FiniteSmallSection
import Mathlib.Algebra.Order.Group.Abs

namespace ABD2
namespace ABCTriple

/-- A concrete coordinate bound for a full tangent.

It is deliberately crude: sum the absolute values of all coordinates.  Phase 7
only needs to show that a finite coordinate bound exists whenever a lift exists;
the quality of the bound is postponed to later lift-cost and power-saving
phases. -/
noncomputable def coordinateBound
    (T : ABCTriple) (x : T.FullTangent) : ℤ :=
  T.support.attach.sum (fun p => |x p|)

/-- Every full tangent is coordinate-small for its crude coordinate bound. -/
theorem smallTangent_coordinateBound
    (T : ABCTriple) (x : T.FullTangent) :
    T.SmallTangent x (T.coordinateBound x) := by
  classical
  intro p
  have hp : p ∈ T.support.attach := by
    simp
  have hnonneg : ∀ q ∈ T.support.attach, 0 ≤ |x q| := by
    intro q _hq
    exact abs_nonneg (x q)
  have hle : |x p| ≤ T.coordinateBound x := by
    dsimp [ABCTriple.coordinateBound]
    exact Finset.single_le_sum hnonneg hp
  constructor
  · exact (abs_le.mp hle).1
  · exact (abs_le.mp hle).2

/-- If the C-fiber over a seed is nonempty, then it has a finite coordinate-small
point.

This is the key Phase 7 separation: finite boundedness is automatic from finite
support, so the real SDC difficulty is not finite existence but the quality of
that bound. -/
theorem hasFiniteSmallFiberOver_of_fiberNonempty
    (T : ABCTriple) (seed : T.FullTangent)
    (h : T.FiberNonempty seed) :
    T.HasFiniteSmallFiberOver seed := by
  rcases h with ⟨lift, hfiber⟩
  exact ⟨T.coordinateBound lift, lift, hfiber, T.smallTangent_coordinateBound lift⟩

/-- A concrete C-lift immediately gives a finite coordinate-small fiber point. -/
theorem hasFiniteSmallFiberOver_of_hasCLift
    (T : ABCTriple) (seed lift : T.FullTangent)
    (h : T.HasCLift seed lift) :
    T.HasFiniteSmallFiberOver seed := by
  exact T.hasFiniteSmallFiberOver_of_fiberNonempty seed ⟨lift, h⟩

/-- A solved qualitative fibration automatically has a finite small section.

Only the existence of some finite bound is asserted here.  No power-saving or
uniform estimate is claimed. -/
theorem hasFiniteSmallSection_of_qualitativeFibrationSolved
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.QualitativeFibrationSolved P) :
    T.HasFiniteSmallSection P := by
  rcases h with ⟨hbase, hfiberAll⟩
  rcases hbase with ⟨seed, hgood⟩
  have hseedMem : seed ∈ T.ABBase P := hgood.1
  have hfiniteFiber : T.HasFiniteSmallFiberOver seed :=
    T.hasFiniteSmallFiberOver_of_fiberNonempty seed (hfiberAll seed hseedMem)
  exact (T.hasFiniteSmallSection_iff_exists_goodBasePoint_and_finiteSmallFiber P).2
    ⟨seed, hgood, hfiniteFiber⟩

/-- For a realized profile, a good base point already gives a finite small
section: realization supplies the fiber, and finite support supplies a crude
coordinate bound. -/
theorem hasFiniteSmallSection_of_hasGoodBasePoint_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (hbase : T.HasGoodBasePoint P) :
    T.HasFiniteSmallSection P := by
  have hqual : T.QualitativeFibrationSolved P :=
    (T.qualitativeFibrationSolved_iff_hasGoodBasePoint_of_profileRealizesCImage
      P hblocks hreal).2 hbase
  exact T.hasFiniteSmallSection_of_qualitativeFibrationSolved P hqual

/-- For a realized profile, finite small sections are equivalent to qualitative
fibration.

Thus Phase 7 identifies finite smallness as automatic at the qualitative level;
later phases must improve the bound, not merely prove that some bound exists. -/
theorem hasFiniteSmallSection_iff_qualitativeFibrationSolved_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P) :
    T.HasFiniteSmallSection P ↔ T.QualitativeFibrationSolved P := by
  constructor
  · intro hfinite
    have hbase : T.HasGoodBasePoint P := by
      rcases (T.hasFiniteSmallSection_iff_exists_goodBasePoint_and_finiteSmallFiber P).1
        hfinite with ⟨seed, hgood, _hfiniteFiber⟩
      exact ⟨seed, hgood⟩
    exact (T.qualitativeFibrationSolved_iff_hasGoodBasePoint_of_profileRealizesCImage
      P hblocks hreal).2 hbase
  · intro hqual
    exact T.hasFiniteSmallSection_of_qualitativeFibrationSolved P hqual

/-- For a realized profile, finite small sections are equivalent to strict
candidates.

This is the finite-bound version of the smallness-free skeleton.  It is not an
SDC-level estimate: the bound may be very large. -/
theorem hasFiniteSmallSection_iff_hasStrictCandidate_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P) :
    T.HasFiniteSmallSection P ↔ T.HasStrictCandidate := by
  exact (T.hasFiniteSmallSection_iff_qualitativeFibrationSolved_of_profileRealizesCImage
      P hblocks hreal).trans
    (T.hasStrictCandidate_iff_qualitativeFibrationSolved_of_profileRealizesCImage
      P hblocks hreal).symm

/-- A strict candidate gives a finite small section for any realized profile. -/
theorem hasFiniteSmallSection_of_hasStrictCandidate_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (hstrict : T.HasStrictCandidate) :
    T.HasFiniteSmallSection P := by
  exact (T.hasFiniteSmallSection_iff_hasStrictCandidate_of_profileRealizesCImage
    P hblocks hreal).2 hstrict

namespace RealizedCImageProfile

/-- Realized-profile wrapper for Phase 7: qualitative fibration is equivalent to
finite small-section existence. -/
theorem hasFiniteSmallSection_iff_qualitativeFibrationSolved
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.HasFiniteSmallSection R.profile ↔ T.QualitativeFibrationSolved R.profile := by
  exact T.hasFiniteSmallSection_iff_qualitativeFibrationSolved_of_profileRealizesCImage
    R.profile R.blocks R.realizes

/-- Realized-profile wrapper: strict candidates are equivalent to finite small
sections. -/
theorem hasFiniteSmallSection_iff_hasStrictCandidate
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.HasFiniteSmallSection R.profile ↔ T.HasStrictCandidate := by
  exact T.hasFiniteSmallSection_iff_hasStrictCandidate_of_profileRealizesCImage
    R.profile R.blocks R.realizes

/-- Realized-profile forward form from strict candidates to finite small sections. -/
theorem hasFiniteSmallSection_of_hasStrictCandidate
    {T : ABCTriple} (R : T.RealizedCImageProfile)
    (hstrict : T.HasStrictCandidate) :
    T.HasFiniteSmallSection R.profile := by
  exact (R.hasFiniteSmallSection_iff_hasStrictCandidate).2 hstrict

/-- Realized-profile forward form from qualitative fibration to finite small
sections. -/
theorem hasFiniteSmallSection_of_qualitativeFibrationSolved
    {T : ABCTriple} (R : T.RealizedCImageProfile)
    (hqual : T.QualitativeFibrationSolved R.profile) :
    T.HasFiniteSmallSection R.profile := by
  exact (R.hasFiniteSmallSection_iff_qualitativeFibrationSolved).2 hqual

end RealizedCImageProfile

/-- Canonical Phase 7 equivalence under `1 < c`: qualitative fibration is the
same as finite small-section existence over the concrete gcd profile. -/
theorem hasFiniteSmallSection_iff_qualitativeFibrationSolved_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.HasFiniteSmallSection ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) ↔
      T.QualitativeFibrationSolved
        ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  exact T.hasFiniteSmallSection_iff_qualitativeFibrationSolved_of_profileRealizesCImage
    ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile)
    hblocks (T.profileRealizesCImage_of_one_lt_c hblocks hc)

/-- Canonical Phase 7 equivalence under `1 < c`: strict candidates are exactly
finite small sections over the concrete gcd profile. -/
theorem hasFiniteSmallSection_iff_hasStrictCandidate_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.HasFiniteSmallSection ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) ↔
      T.HasStrictCandidate := by
  exact T.hasFiniteSmallSection_iff_hasStrictCandidate_of_profileRealizesCImage
    ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile)
    hblocks (T.profileRealizesCImage_of_one_lt_c hblocks hc)

/-- Canonical forward form: strict candidates produce finite small sections over
the concrete gcd profile. -/
theorem hasFiniteSmallSection_of_hasStrictCandidate_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c)
    (hstrict : T.HasStrictCandidate) :
    T.HasFiniteSmallSection ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  exact (T.hasFiniteSmallSection_iff_hasStrictCandidate_of_one_lt_c hblocks hc).2 hstrict

end ABCTriple
end ABD2
