import ABD.ABD2.Lattice.IntegerLinearImage

namespace ABD2

open BigOperators

/-- A generator certificate for the image of a finite integer linear form.

`IntegerImageGenerator coeff g` means that `g` both divides every coefficient
and is itself attained by the linear form.  This deliberately separates the easy
image-theoretic argument from the later, harder proof that the concrete gcd has
such a Bezout representation. -/
structure IntegerImageGenerator {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (g : ℤ) : Prop where
  commonDivisor : CoeffCommonDivisor coeff g
  bezout : ∃ u : ι → ℤ, IntegerLinearForm coeff u = g

/-- Bezout representation gives the reverse inclusion: every multiple of `g`
is in the image of the linear form.

This is the main Lean-simplifying lemma for the hard direction.  It does not
mention gcds at all. -/
theorem multiples_subset_integerLinearImage_of_bezout
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) {g : ℤ}
    (hbezout : ∃ u : ι → ℤ, IntegerLinearForm coeff u = g) :
    {target : ℤ | g ∣ target} ⊆ IntegerLinearImage coeff := by
  intro target htarget
  rcases hbezout with ⟨u, hu⟩
  rcases htarget with ⟨k, hk⟩
  refine ⟨fun i => u i * k, ?_⟩
  rw [hk]
  unfold IntegerLinearForm at hu ⊢
  calc
    ∑ i, coeff i * (u i * k)
        = ∑ i, (coeff i * u i) * k := by
          simp [mul_assoc]
    _ = (∑ i, coeff i * u i) * k := by
          rw [← Finset.sum_mul]
    _ = g * k := by
          rw [hu]

/-- If `g` is a generator certificate, the image of the linear form is exactly
`gℤ`. -/
theorem integerLinearImage_eq_multiples_of_generator
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) {g : ℤ}
    (hgen : IntegerImageGenerator coeff g) :
    IntegerLinearImage coeff = {target : ℤ | g ∣ target} := by
  ext target
  constructor
  · intro htarget
    exact commonDivisor_dvd_of_mem_integerLinearImage coeff hgen.commonDivisor htarget
  · intro htarget
    exact multiples_subset_integerLinearImage_of_bezout coeff hgen.bezout htarget

/-- Forward routing from a generator certificate to membership in the image. -/
theorem mem_integerLinearImage_of_generator_dvd
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) {g target : ℤ}
    (hgen : IntegerImageGenerator coeff g) (hdiv : g ∣ target) :
    target ∈ IntegerLinearImage coeff := by
  exact (integerLinearImage_eq_multiples_of_generator coeff hgen).symm ▸ hdiv

/-- Divisibility form obtained from a generator certificate. -/
theorem generator_dvd_of_mem_integerLinearImage
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) {g target : ℤ}
    (hgen : IntegerImageGenerator coeff g)
    (htarget : target ∈ IntegerLinearImage coeff) :
    g ∣ target := by
  exact commonDivisor_dvd_of_mem_integerLinearImage coeff hgen.commonDivisor htarget

end ABD2
