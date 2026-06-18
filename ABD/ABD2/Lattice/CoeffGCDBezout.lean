import ABD.ABD2.Lattice.CoeffGCDCommonDivisor

namespace ABD2

/-- Step-C package: the chosen gcd/common-divisor witness also has a Bezout
representation.

This is the only genuinely hard ingredient left after Step A/B.  It deliberately
stores the Bezout expression as data, so the image-equality theorem can be reused
without reopening the finite-gcd construction. -/
structure CoeffGCDBezoutWitness
    {ι : Type*} [Fintype ι] {coeff : ι → ℤ}
    (W : CoeffGCDCommonDivisorWitness coeff) : Prop where
  bezout : ∃ u : ι → ℤ, IntegerLinearForm coeff u = W.gcd

namespace CoeffGCDBezoutWitness

/-- A Step-C Bezout witness upgrades a Step-B common-divisor witness to the
Step-A generator certificate. -/
def generator
    {ι : Type*} [Fintype ι] {coeff : ι → ℤ}
    {W : CoeffGCDCommonDivisorWitness coeff}
    (H : CoeffGCDBezoutWitness W) :
    IntegerImageGenerator coeff W.gcd :=
  W.generatorOfBezout H.bezout

/-- Step-C completion theorem: once the Bezout witness is supplied, the image is
exactly the multiples of the candidate gcd. -/
theorem integerLinearImage_eq_multiples
    {ι : Type*} [Fintype ι] {coeff : ι → ℤ}
    {W : CoeffGCDCommonDivisorWitness coeff}
    (H : CoeffGCDBezoutWitness W) :
    IntegerLinearImage coeff = {target : ℤ | W.gcd ∣ target} := by
  exact integerLinearImage_eq_multiples_of_generator coeff H.generator

/-- Reverse inclusion form, often the most convenient way to use the Step-C
witness. -/
theorem multiples_subset_integerLinearImage
    {ι : Type*} [Fintype ι] {coeff : ι → ℤ}
    {W : CoeffGCDCommonDivisorWitness coeff}
    (H : CoeffGCDBezoutWitness W) :
    {target : ℤ | W.gcd ∣ target} ⊆ IntegerLinearImage coeff := by
  exact multiples_subset_integerLinearImage_of_bezout coeff H.bezout

/-- Membership form of the reverse inclusion. -/
theorem mem_integerLinearImage_of_dvd
    {ι : Type*} [Fintype ι] {coeff : ι → ℤ}
    {W : CoeffGCDCommonDivisorWitness coeff}
    (H : CoeffGCDBezoutWitness W) {target : ℤ}
    (hdiv : W.gcd ∣ target) :
    target ∈ IntegerLinearImage coeff := by
  exact H.multiples_subset_integerLinearImage hdiv

/-- Divisibility form of the forward inclusion, inherited from the common-divisor
half. -/
theorem gcd_dvd_of_mem_integerLinearImage
    {ι : Type*} [Fintype ι] {coeff : ι → ℤ}
    {W : CoeffGCDCommonDivisorWitness coeff}
    {target : ℤ}
    (htarget : target ∈ IntegerLinearImage coeff) :
    W.gcd ∣ target := by
  exact commonDivisor_dvd_of_mem_integerLinearImage coeff W.commonDivisor htarget

end CoeffGCDBezoutWitness
end ABD2
