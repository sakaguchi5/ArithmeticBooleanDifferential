import ABD.ABD2.Reduction.CImageGCDFinal
import ABD.ABD2.Lattice.CoeffFinsetGCDNonzero

namespace ABD2
namespace ABCTriple

/-- View a C-support coordinate as a full-support coordinate. -/
def cSupportToFullSupport
    (T : ABCTriple) (p : {p : ℕ // p ∈ T.supportC}) :
    {p : ℕ // p ∈ T.support} :=
  ⟨p.1, by
    unfold ABCTriple.support
    simp [p.2]⟩

@[simp]
theorem cSupportToFullSupport_val
    (T : ABCTriple) (p : {p : ℕ // p ∈ T.supportC}) :
    (T.cSupportToFullSupport p).1 = p.1 := by
  rfl

/-- The full-support C-coefficient restricts to the C-support coefficient. -/
theorem cCoeffOnFullSupport_cSupportToFullSupport
    (T : ABCTriple) (p : {p : ℕ // p ∈ T.supportC}) :
    T.cCoeffOnFullSupport (T.cSupportToFullSupport p) = T.cCoeffOnC p := by
  rfl

/-- If one full-support C-coefficient is nonzero, then the final C-coefficient gcd
is nonzero. -/
theorem cCoeffFullGCD_ne_zero_of_exists_nonzero_fullCoeff
    (T : ABCTriple)
    (h : ∃ p : {p : ℕ // p ∈ T.support}, T.cCoeffOnFullSupport p ≠ 0) :
    T.cCoeffFullGCD ≠ 0 := by
  unfold ABCTriple.cCoeffFullGCD
  exact coeffFinsetGCD_ne_zero_of_exists_nonzero_coeff
    T.cCoeffOnFullSupport h

/-- If one C-support coefficient is nonzero, then the final full-support
C-coefficient gcd is nonzero. -/
theorem cCoeffFullGCD_ne_zero_of_exists_nonzero_cCoeffOnC
    (T : ABCTriple)
    (h : ∃ p : {p : ℕ // p ∈ T.supportC}, T.cCoeffOnC p ≠ 0) :
    T.cCoeffFullGCD ≠ 0 := by
  rcases h with ⟨p, hp⟩
  exact T.cCoeffFullGCD_ne_zero_of_exists_nonzero_fullCoeff
    ⟨T.cSupportToFullSupport p, by
      simpa [T.cCoeffOnFullSupport_cSupportToFullSupport p] using hp⟩

/-- Zero gcd forces every full-support C-coefficient to vanish. -/
theorem cCoeffOnFullSupport_eq_zero_of_cCoeffFullGCD_eq_zero
    (T : ABCTriple) (hg : T.cCoeffFullGCD = 0)
    (p : {p : ℕ // p ∈ T.support}) :
    T.cCoeffOnFullSupport p = 0 := by
  unfold ABCTriple.cCoeffFullGCD at hg
  exact coeff_eq_zero_of_coeffFinsetGCD_eq_zero
    T.cCoeffOnFullSupport hg p

/-- Zero gcd also forces every C-support coefficient to vanish. -/
theorem cCoeffOnC_eq_zero_of_cCoeffFullGCD_eq_zero
    (T : ABCTriple) (hg : T.cCoeffFullGCD = 0)
    (p : {p : ℕ // p ∈ T.supportC}) :
    T.cCoeffOnC p = 0 := by
  have hfull := T.cCoeffOnFullSupport_eq_zero_of_cCoeffFullGCD_eq_zero
    hg (T.cSupportToFullSupport p)
  simpa [T.cCoeffOnFullSupport_cSupportToFullSupport p] using hfull

end ABCTriple
end ABD2
