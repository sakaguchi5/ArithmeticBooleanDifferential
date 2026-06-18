import ABD.ABD2.Reduction.CImageGCDPositiveC

namespace ABD2
namespace ABCTriple

/-- Theorem 3, ABD2 surface form: the C-image is exactly the multiples of the
finite gcd of the C-derivative coefficients. -/
theorem Theorem3_CImage_eq_cCoeffFullGCDMultiples
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose) :
    T.CImage = {target : ℤ | T.cCoeffFullGCD ∣ target} := by
  exact T.CImage_eq_cCoeffFullGCDMultiples hblocks

/-- Pointwise form of Theorem 3. -/
theorem Theorem3_mem_CImage_iff_cCoeffFullGCD_dvd
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose) (target : ℤ) :
    target ∈ T.CImage ↔ T.cCoeffFullGCD ∣ target := by
  exact T.mem_CImage_iff_cCoeffFullGCD_dvd hblocks target

/-- Positivity of `c` gives the nonzero C-coefficient needed by the concrete gcd
witness. -/
theorem Theorem3_exists_nonzero_cCoeffOnC_of_one_lt_c
    (T : ABCTriple) (hc : 1 < T.c) :
    ∃ p : {p : ℕ // p ∈ T.supportC}, T.cCoeffOnC p ≠ 0 := by
  exact T.exists_nonzero_cCoeffOnC_of_one_lt_c hc

/-- Concrete C-image gcd witness under the abc-style positivity assumption
`1 < c`. -/
def Theorem3_cImageGCDWitness_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.CImageGCDWitness :=
  T.cImageGCDWitness_of_one_lt_c hblocks hc

/-- The concrete C-image profile is realized under `1 < c`. -/
theorem Theorem3_profileRealizesCImage_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.ProfileRealizesCImage
      ((T.Theorem3_cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  exact (T.Theorem3_cImageGCDWitness_of_one_lt_c hblocks hc).profile_realizes

end ABCTriple
end ABD2
