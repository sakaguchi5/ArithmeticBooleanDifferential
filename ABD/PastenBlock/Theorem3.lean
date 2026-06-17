import ABD.PastenBlock.CoeffGCDBridge

namespace ABD

/-- Final wrapper for Theorem 3, first clause: `c`-adjustment is the integer image
of the linear map `L_c : ℤ^{S_c} → ℤ`. -/
theorem ABCTriple.Theorem3_cAdjustment_is_integerImage
    (T : ABCTriple) :
    T.cImage = T.cLinearMapRange := by
  exact T.cImage_eq_cLinearMapRange

/-- Final wrapper for Theorem 3, range/submodule form: the same image is the
carrier of the linear-map range submodule. -/
theorem ABCTriple.Theorem3_cAdjustment_is_linearMapRange
    (T : ABCTriple) :
    T.cImage = (T.cLinearMapSubmoduleRange : Set ℤ) := by
  exact T.cImage_eq_cLinearMapSubmoduleRange_carrier

/-- Final wrapper for Theorem 3, gcd image form: the image of `L_c` is precisely
`gcd(coeff_c(p))ℤ`, using the normalized natural-number gcd. -/
theorem ABCTriple.Theorem3_cImage_eq_gcdMultiples
    (T : ABCTriple) :
    T.cImage = T.cCoeffGCDMultiples := by
  exact T.cImage_eq_cCoeffGCDMultiples

/-- Pointwise membership form of the gcd image theorem. -/
theorem ABCTriple.Theorem3_mem_cImage_iff_gcd_dvd
    (T : ABCTriple) (target : ℤ) :
    target ∈ T.cImage ↔ (T.cCoeffGCD : ℤ) ∣ target := by
  exact T.mem_cImage_iff_cCoeffGCD_dvd target

/-- Final wrapper for Theorem 3, adjustment criterion: an `a/b` seed can be
absorbed on the `c` side exactly when its target is divisible by the
`c`-coefficient gcd. -/
theorem ABCTriple.Theorem3_cAdjustable_iff_gcdDividesTarget
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) :
    T.CAdjustable xA xB ↔ (T.cCoeffGCD : ℤ) ∣ T.abSeedTarget xA xB := by
  exact T.cAdjustable_iff_cCoeffGCD_dvd_abSeedTarget xA xB

/-- Final wrapper for Theorem 3, lift form: a divisibility proof by the
`c`-coefficient gcd constructs a `c`-side adjustment lift. -/
theorem ABCTriple.Theorem3_cAdjustmentLift_of_gcdDividesTarget
    (T : ABCTriple) {xA : T.ATangent} {xB : T.BTangent}
    (hdiv : (T.cCoeffGCD : ℤ) ∣ T.abSeedTarget xA xB) :
    Nonempty (T.CAdjustmentLift xA xB) := by
  exact T.cAdjustmentLift_of_cCoeffGCD_dvd_abSeedTarget hdiv

end ABD
