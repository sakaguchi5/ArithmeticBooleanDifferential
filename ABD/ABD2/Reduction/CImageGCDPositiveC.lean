import Mathlib.Data.Nat.Prime.Basic
import ABD.ABD2.Reduction.CImageGCDComplete

namespace ABD2
namespace ABCTriple

/-- A C-support coordinate with positive quotient `c / p` has nonzero C-coefficient.

The coefficient is

`derivCoeff c p = v_p(c) * (c / p)`.

Membership in `supportC` says `v_p(c) ≠ 0`, while the explicit quotient positivity
says `c / p ≠ 0`; hence the product is nonzero in `ℤ`. -/
theorem cCoeffOnC_ne_zero_of_div_pos
    (T : ABCTriple) (p : {p : ℕ // p ∈ T.supportC})
    (hdivpos : 0 < T.c / p.1) :
    T.cCoeffOnC p ≠ 0 := by
  have hval_ne : val T.c p.1 ≠ 0 := by
    unfold val
    exact Finsupp.mem_support_iff.mp (by
      simp [ABCTriple.supportC, PrimeSupport])
  have hval_int_ne : ((val T.c p.1 : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast hval_ne
  have hquot_int_ne : (((T.c / p.1 : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdivpos)
  unfold ABCTriple.cCoeffOnC derivCoeff
  exact mul_ne_zero hval_int_ne hquot_int_ne

/-- If `1 < c`, then the C side has at least one nonzero derivative coefficient.

This is the arithmetic bridge left after the finite-gcd image theorem: choose the
least prime factor of `c`.  It lies in `supportC`, and since it divides the
positive number `c`, the quotient `c / p` is positive; therefore its derivative
coefficient is nonzero. -/
theorem exists_nonzero_cCoeffOnC_of_one_lt_c
    (T : ABCTriple) (hc : 1 < T.c) :
    ∃ p : {p : ℕ // p ∈ T.supportC}, T.cCoeffOnC p ≠ 0 := by
  classical
  let q : ℕ := Nat.minFac T.c
  have hcpos : 0 < T.c := Nat.lt_trans Nat.zero_lt_one hc
  have hcne0 : T.c ≠ 0 := Nat.ne_of_gt hcpos
  have hqprime : Nat.Prime q := by
    simpa [q] using Nat.minFac_prime (Nat.ne_of_gt hc)
  have hqdvd : q ∣ T.c := by
    simpa [q] using Nat.minFac_dvd T.c
  have hqmemPrimeFactors : q ∈ T.c.primeFactors := by
    simp [Nat.mem_primeFactors, hcne0, hqprime, hqdvd]
  have hqmemC : q ∈ T.supportC := by
    unfold ABCTriple.supportC PrimeSupport
    rw [Nat.support_factorization]
    exact hqmemPrimeFactors
  let qC : {p : ℕ // p ∈ T.supportC} := ⟨q, hqmemC⟩
  have hqpos : 0 < q := hqprime.pos
  have hqle : q ≤ T.c := Nat.le_of_dvd hcpos hqdvd
  have hdivpos : 0 < T.c / q := Nat.div_pos hqle hqpos
  refine ⟨qC, ?_⟩
  exact T.cCoeffOnC_ne_zero_of_div_pos qC hdivpos

/-- Final concrete C-image gcd witness from the abc-style positivity assumption
`1 < c`. -/
def cImageGCDWitness_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.CImageGCDWitness :=
  T.cImageGCDWitness_of_exists_nonzero_cCoeffOnC hblocks
    (T.exists_nonzero_cCoeffOnC_of_one_lt_c hc)

/-- The concrete C-image profile realized from the abc-style positivity assumption
`1 < c`. -/
theorem profileRealizesCImage_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.ProfileRealizesCImage
      ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  exact (T.cImageGCDWitness_of_one_lt_c hblocks hc).profile_realizes

/-- Final strict-candidate criterion using the abc-style positivity assumption
`1 < c`. -/
theorem hasStrictCandidate_iff_not_BadSeed_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.HasStrictCandidate ↔
      ¬ T.BadSeed ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  let W := T.cImageGCDWitness_of_one_lt_c hblocks hc
  exact W.hasStrictCandidate_iff_not_BadSeed hblocks

/-- Forward routing form of the final criterion under `1 < c`. -/
theorem hasStrictCandidate_of_not_BadSeed_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c)
    (hgood : ¬ T.BadSeed ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile)) :
    T.HasStrictCandidate := by
  exact ((T.hasStrictCandidate_iff_not_BadSeed_of_one_lt_c hblocks hc).2 hgood)

/-- Reverse obstruction form of the final criterion under `1 < c`. -/
theorem not_BadSeed_of_hasStrictCandidate_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c)
    (hstrict : T.HasStrictCandidate) :
    ¬ T.BadSeed ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  exact ((T.hasStrictCandidate_iff_not_BadSeed_of_one_lt_c hblocks hc).1 hstrict)

end ABCTriple
end ABD2
