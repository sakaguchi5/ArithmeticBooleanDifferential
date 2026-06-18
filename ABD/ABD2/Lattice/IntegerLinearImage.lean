import Mathlib.Algebra.BigOperators.Ring.Finset

namespace ABD2

open BigOperators

/-- A finite integer linear form. -/
def IntegerLinearForm {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (x : ι → ℤ) : ℤ :=
  ∑ i, coeff i * x i

/-- The image of a finite integer linear form. -/
def IntegerLinearImage {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) : Set ℤ :=
  {target | ∃ x : ι → ℤ, IntegerLinearForm coeff x = target}

/-- `d` is a common divisor of all coefficients. -/
def CoeffCommonDivisor {ι : Type*} (coeff : ι → ℤ) (d : ℤ) : Prop :=
  ∀ i, d ∣ coeff i

/-- The easy half of the integer-image gcd theorem:
any common divisor of the coefficients divides every value of the linear form. -/
theorem commonDivisor_dvd_integerLinearForm
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) {d : ℤ}
    (hdiv : CoeffCommonDivisor coeff d) (x : ι → ℤ) :
    d ∣ IntegerLinearForm coeff x := by
  unfold IntegerLinearForm
  exact Finset.dvd_sum fun i _hi => dvd_mul_of_dvd_left (hdiv i) (x i)

/-- The easy half at the image level:
any common divisor of the coefficients divides every element of the image. -/
theorem commonDivisor_dvd_of_mem_integerLinearImage
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) {d target : ℤ}
    (hdiv : CoeffCommonDivisor coeff d)
    (htarget : target ∈ IntegerLinearImage coeff) :
    d ∣ target := by
  rcases htarget with ⟨x, hx⟩
  rw [← hx]
  exact commonDivisor_dvd_integerLinearForm coeff hdiv x

/-- Set-inclusion form of the easy half. -/
theorem integerLinearImage_subset_commonDivisorMultiples
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) {d : ℤ}
    (hdiv : CoeffCommonDivisor coeff d) :
    IntegerLinearImage coeff ⊆ {target : ℤ | d ∣ target} := by
  intro target htarget
  exact commonDivisor_dvd_of_mem_integerLinearImage coeff hdiv htarget

end ABD2
