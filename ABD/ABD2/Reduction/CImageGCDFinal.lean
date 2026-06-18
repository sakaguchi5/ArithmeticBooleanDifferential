import ABD.ABD2.Reduction.CImageGCDFromBezout
import ABD.ABD2.Lattice.CoeffFinsetGCD

namespace ABD2
namespace ABCTriple

/-- The final ABD2 finite-gcd candidate for the C-image theorem, computed from the
full-support C-coefficients.

Coordinates outside `supportC` have zero C-derivative contribution, so the
full-support form is still the correct one for `CImage_eq_integerLinearImage_cCoeff`. -/
def cCoeffFullGCD (T : ABCTriple) : ℤ :=
  CoeffFinsetGCD T.cCoeffOnFullSupport

@[simp]
theorem cCoeffFullGCD_eq_coeffFinsetGCD
    (T : ABCTriple) :
    T.cCoeffFullGCD = CoeffFinsetGCD T.cCoeffOnFullSupport := by
  rfl

/-- The final finite-gcd candidate divides every full-support C-coefficient. -/
theorem cCoeffFullGCD_dvd_cCoeffOnFullSupport
    (T : ABCTriple) (p : {p : ℕ // p ∈ T.support}) :
    T.cCoeffFullGCD ∣ T.cCoeffOnFullSupport p := by
  unfold ABCTriple.cCoeffFullGCD
  exact coeffFinsetGCD_dvd_coeff T.cCoeffOnFullSupport p

/-- The final finite-gcd candidate as a Step-B common-divisor witness. -/
def cCoeffFullGCDCommonDivisorWitness
    (T : ABCTriple) :
    CoeffGCDCommonDivisorWitness T.cCoeffOnFullSupport :=
  coeffFinsetGCDCommonDivisorWitness T.cCoeffOnFullSupport

/-- The final finite-gcd candidate has a finite Bezout representation. -/
def cCoeffFullGCDBezoutWitness
    (T : ABCTriple) :
    CoeffGCDBezoutWitness T.cCoeffFullGCDCommonDivisorWitness :=
  coeffFinsetGCDBezoutWitness T.cCoeffOnFullSupport

/-- The C-image is exactly the multiples of the final full-support C-coefficient gcd. -/
theorem CImage_eq_cCoeffFullGCDMultiples
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose) :
    T.CImage = {target : ℤ | T.cCoeffFullGCD ∣ target} := by
  rw [T.CImage_eq_integerLinearImage_cCoeff hblocks]
  simpa [ABCTriple.cCoeffFullGCD] using
    (integerLinearImage_eq_coeffFinsetGCD_multiples T.cCoeffOnFullSupport)

/-- Pointwise membership form of the final C-image gcd theorem. -/
theorem mem_CImage_iff_cCoeffFullGCD_dvd
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose) (target : ℤ) :
    target ∈ T.CImage ↔ T.cCoeffFullGCD ∣ target := by
  rw [T.CImage_eq_cCoeffFullGCDMultiples hblocks]
  rfl

/-- The final finite-gcd candidate realizes the ABD2 C-image profile, once its
nonzero proof is supplied.

The nonzero proof is intentionally separated: in abc applications it should come
from the arithmetic assumptions such as `1 < T.c` / nonempty C-support and a
nonzero C-coefficient. -/
theorem profileRealizesCImage_cCoeffFullGCD
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hg : T.cCoeffFullGCD ≠ 0) :
    T.ProfileRealizesCImage
      { gcd := T.cCoeffFullGCD
        gcd_ne_zero := hg } := by
  intro target
  rw [T.mem_CImage_iff_cCoeffFullGCD_dvd hblocks target]

/-- Final bridge to the existing ABD2 gcd interface. -/
def cImageGCDWitness_cCoeffFullGCD
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hg : T.cCoeffFullGCD ≠ 0) :
    T.CImageGCDWitness where
  gcd := T.cCoeffFullGCD
  gcd_ne_zero := hg
  realizes := T.profileRealizesCImage_cCoeffFullGCD hblocks hg

/-- Final concrete-gcd strict-candidate criterion, routed through the existing
`CImageGCDWitness` interface. -/
theorem hasStrictCandidate_iff_not_BadSeed_cCoeffFullGCD
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hg : T.cCoeffFullGCD ≠ 0) :
    T.HasStrictCandidate ↔
      ¬ T.BadSeed ((T.cImageGCDWitness_cCoeffFullGCD hblocks hg).profile) := by
  let W := T.cImageGCDWitness_cCoeffFullGCD hblocks hg
  exact W.hasStrictCandidate_iff_not_BadSeed hblocks

/-- Forward routing form of the final concrete-gcd strict-candidate criterion. -/
theorem hasStrictCandidate_of_not_BadSeed_cCoeffFullGCD
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hg : T.cCoeffFullGCD ≠ 0)
    (hgood : ¬ T.BadSeed ((T.cImageGCDWitness_cCoeffFullGCD hblocks hg).profile)) :
    T.HasStrictCandidate := by
  exact ((T.hasStrictCandidate_iff_not_BadSeed_cCoeffFullGCD hblocks hg).2 hgood)

/-- Reverse obstruction form of the final concrete-gcd strict-candidate criterion. -/
theorem not_BadSeed_of_hasStrictCandidate_cCoeffFullGCD
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hg : T.cCoeffFullGCD ≠ 0)
    (hstrict : T.HasStrictCandidate) :
    ¬ T.BadSeed ((T.cImageGCDWitness_cCoeffFullGCD hblocks hg).profile) := by
  exact ((T.hasStrictCandidate_iff_not_BadSeed_cCoeffFullGCD hblocks hg).1 hstrict)

end ABCTriple
end ABD2
