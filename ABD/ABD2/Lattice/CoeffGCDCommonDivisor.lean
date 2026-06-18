import ABD.ABD2.Lattice.IntegerImageGenerator

namespace ABD2

/-- Step-B package: a gcd candidate whose easy half has been proved.

This file intentionally does not prove that the candidate is the actual gcd and
it does not construct Bezout coefficients.  It records the common-divisor half
as data, so the later Bezout theorem can be plugged in without reworking the
image argument. -/
structure CoeffGCDCommonDivisorWitness {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) where
  gcd : ℤ
  commonDivisor : CoeffCommonDivisor coeff gcd

namespace CoeffGCDCommonDivisorWitness

/-- The easy image inclusion supplied by a common-divisor witness. -/
theorem integerLinearImage_subset_multiples
    {ι : Type*} [Fintype ι] {coeff : ι → ℤ}
    (W : CoeffGCDCommonDivisorWitness coeff) :
    IntegerLinearImage coeff ⊆ {target : ℤ | W.gcd ∣ target} := by
  exact integerLinearImage_subset_commonDivisorMultiples coeff W.commonDivisor

/-- Adding a Bezout expression upgrades a common-divisor witness to a full image
generator certificate. -/
def generatorOfBezout
    {ι : Type*} [Fintype ι] {coeff : ι → ℤ}
    (W : CoeffGCDCommonDivisorWitness coeff)
    (hbezout : ∃ u : ι → ℤ, IntegerLinearForm coeff u = W.gcd) :
    IntegerImageGenerator coeff W.gcd where
  commonDivisor := W.commonDivisor
  bezout := hbezout

/-- Once the later Bezout theorem is supplied, a Step-B witness yields the full
image equality. -/
theorem integerLinearImage_eq_multiples_of_bezout
    {ι : Type*} [Fintype ι] {coeff : ι → ℤ}
    (W : CoeffGCDCommonDivisorWitness coeff)
    (hbezout : ∃ u : ι → ℤ, IntegerLinearForm coeff u = W.gcd) :
    IntegerLinearImage coeff = {target : ℤ | W.gcd ∣ target} := by
  exact integerLinearImage_eq_multiples_of_generator coeff
    (W.generatorOfBezout hbezout)

/-- Reverse image inclusion after the future Bezout theorem is available. -/
theorem multiples_subset_integerLinearImage_of_bezout
    {ι : Type*} [Fintype ι] {coeff : ι → ℤ}
    (W : CoeffGCDCommonDivisorWitness coeff)
    (hbezout : ∃ u : ι → ℤ, IntegerLinearForm coeff u = W.gcd) :
    {target : ℤ | W.gcd ∣ target} ⊆ IntegerLinearImage coeff := by
  exact ABD2.multiples_subset_integerLinearImage_of_bezout coeff hbezout

end CoeffGCDCommonDivisorWitness
end ABD2
