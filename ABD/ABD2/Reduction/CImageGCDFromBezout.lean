import ABD.ABD2.Reduction.CoeffLinearForm
import ABD.ABD2.Reduction.CImageGCDInterface
import ABD.ABD2.Reduction.StrictIffFromProfile
import ABD.ABD2.Lattice.CoeffGCDBezout
import ABD.ABD2.Pasten.PastenT

namespace ABD2
namespace ABCTriple

/-- The full-support integer linear form with C-coefficients is the same as the
ABD2 C-linear form.

This is where the formal-derivative locality theorem is used: although the
integer linear form is written on the full support, the `c`-derivative only sees
its C-mask. -/
theorem integerLinearForm_cCoeffOnFullSupport_eq_cLinearForm
    (T : ABCTriple) (x : T.FullTangent) :
    IntegerLinearForm T.cCoeffOnFullSupport x = T.cLinearForm x := by
  unfold IntegerLinearForm cCoeffOnFullSupport ABCTriple.cLinearForm formalDeriv
  exact (T.formalDeriv_c_eq_maskC x).symm

/-- ABD2 C-image is the same as the full-support integer-linear image for the
C-coefficients.

The reverse direction uses the C-mask of an arbitrary full-support witness; the
block decomposition makes that C-mask C-pure. -/
theorem CImage_eq_integerLinearImage_cCoeff
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose) :
    T.CImage = IntegerLinearImage T.cCoeffOnFullSupport := by
  ext target
  constructor
  · intro htarget
    rcases (T.mem_CImage_iff target).1 htarget with ⟨x, _hpure, hx⟩
    refine ⟨x, ?_⟩
    rw [T.integerLinearForm_cCoeffOnFullSupport_eq_cLinearForm x]
    exact hx
  · intro htarget
    rcases htarget with ⟨x, hx⟩
    refine (T.mem_CImage_iff target).2 ?_
    refine ⟨T.maskC x, T.isCPure_maskC hblocks x, ?_⟩
    rw [T.cLinearForm_maskC_eq_self x]
    rw [← T.integerLinearForm_cCoeffOnFullSupport_eq_cLinearForm x]
    exact hx

/-- A Step-B common-divisor witness plus a Step-C Bezout witness realizes the
ABD2 C-image profile. -/
theorem profileRealizesCImage_of_coeffGCDBezout
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (W : CoeffGCDCommonDivisorWitness T.cCoeffOnFullSupport)
    (H : CoeffGCDBezoutWitness W)
    (hg : W.gcd ≠ 0) :
    T.ProfileRealizesCImage
      { gcd := W.gcd
        gcd_ne_zero := hg } := by
  intro target
  rw [T.CImage_eq_integerLinearImage_cCoeff hblocks]
  rw [H.integerLinearImage_eq_multiples]
  rfl

/-- Step-C bridge to the existing ABD2 gcd interface.

The future concrete gcd theorem only needs to produce a common-divisor witness,
a Bezout witness, and nonzero proof for the chosen C-coefficient gcd. -/
def cImageGCDWitness_of_coeffGCDBezout
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (W : CoeffGCDCommonDivisorWitness T.cCoeffOnFullSupport)
    (H : CoeffGCDBezoutWitness W)
    (hg : W.gcd ≠ 0) :
    T.CImageGCDWitness where
  gcd := W.gcd
  gcd_ne_zero := hg
  realizes := T.profileRealizesCImage_of_coeffGCDBezout hblocks W H hg

/-- Once Step C is supplied, the concrete witness gives the strict-candidate
criterion through the existing `CImageGCDWitness` interface. -/
theorem hasStrictCandidate_iff_not_BadSeed_of_coeffGCDBezout
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (W : CoeffGCDCommonDivisorWitness T.cCoeffOnFullSupport)
    (H : CoeffGCDBezoutWitness W)
    (hg : W.gcd ≠ 0) :
    T.HasStrictCandidate ↔
      ¬ T.BadSeed ((T.cImageGCDWitness_of_coeffGCDBezout hblocks W H hg).profile) := by
    let w := T.cImageGCDWitness_of_coeffGCDBezout hblocks W H hg
    exact w.hasStrictCandidate_iff_not_BadSeed hblocks

end ABCTriple
end ABD2
