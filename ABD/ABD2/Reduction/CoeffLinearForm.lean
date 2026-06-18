import ABD.ABD2.Reduction.CImageSupportBridge
import ABD.ABD2.Lattice.IntegerLinearImage

namespace ABD2
namespace ABCTriple

open BigOperators

/-- The `c`-coefficient attached to a full-support prime coordinate. -/
def cCoeffOnFullSupport (T : ABCTriple) (p : {p : ℕ // p ∈ T.support}) : ℤ :=
  derivCoeff T.c p.1

/-- The `c`-coefficient attached to a C-support prime coordinate. -/
def cCoeffOnC (T : ABCTriple) (p : {p : ℕ // p ∈ T.supportC}) : ℤ :=
  derivCoeff T.c p.1

/-- The C-linear form is the finite integer linear form with coefficients
`derivCoeff T.c p`, applied to the C-masked full tangent. -/
theorem cLinearForm_eq_integerLinearForm_maskC
    (T : ABCTriple) (x : T.FullTangent) :
    T.cLinearForm x =
      IntegerLinearForm T.cCoeffOnFullSupport (T.maskC x) := by
  unfold ABCTriple.cLinearForm IntegerLinearForm cCoeffOnFullSupport formalDeriv
  rfl

/-- On an extended C-support tangent, the C-linear form is the same coefficient
linear form applied to the extended vector itself. -/
theorem cLinearForm_extendC_eq_integerLinearForm_extendC
    (T : ABCTriple) (xC : T.CSupportTangent) :
    T.cLinearForm (T.extendC xC) =
      IntegerLinearForm T.cCoeffOnFullSupport (T.extendC xC) := by
  rw [T.cLinearForm_eq_integerLinearForm_maskC]
  rw [T.maskC_extendC_eq_extendC]

/-- A support-level C-linear form.  This is definitionally the full C-linear form
applied after zero-extension.  A later file may replace this by an explicitly
reindexed sum over `supportC`; for now it pins down the bridge target safely. -/
def cSupportLinearForm (T : ABCTriple) (xC : T.CSupportTangent) : ℤ :=
  T.cLinearForm (T.extendC xC)

@[simp]
theorem cSupportLinearForm_apply
    (T : ABCTriple) (xC : T.CSupportTangent) :
    T.cSupportLinearForm xC = T.cLinearForm (T.extendC xC) := by
  rfl

/-- The easy half of the gcd-image theorem, specialized to the ABD2 C-linear form:
any common divisor of the full-support C-coefficients divides every C-linear value. -/
theorem commonDivisor_dvd_cLinearForm
    (T : ABCTriple) {d : ℤ}
    (hdiv : CoeffCommonDivisor T.cCoeffOnFullSupport d)
    (x : T.FullTangent) :
    d ∣ T.cLinearForm x := by
  rw [T.cLinearForm_eq_integerLinearForm_maskC x]
  exact commonDivisor_dvd_integerLinearForm T.cCoeffOnFullSupport hdiv (T.maskC x)

/-- Image-level easy half for ABD2 `CImage`. -/
theorem commonDivisor_dvd_of_mem_CImage
    (T : ABCTriple) {d target : ℤ}
    (hdiv : CoeffCommonDivisor T.cCoeffOnFullSupport d)
    (htarget : target ∈ T.CImage) :
    d ∣ target := by
  rcases (T.mem_CImage_iff target).1 htarget with ⟨x, _hpure, hvalue⟩
  rw [← hvalue]
  exact T.commonDivisor_dvd_cLinearForm hdiv x

/-- Set-inclusion form of the easy half for ABD2 `CImage`. -/
theorem CImage_subset_commonDivisorMultiples
    (T : ABCTriple) {d : ℤ}
    (hdiv : CoeffCommonDivisor T.cCoeffOnFullSupport d) :
    T.CImage ⊆ {target : ℤ | d ∣ target} := by
  intro target htarget
  exact T.commonDivisor_dvd_of_mem_CImage hdiv htarget

end ABCTriple
end ABD2
