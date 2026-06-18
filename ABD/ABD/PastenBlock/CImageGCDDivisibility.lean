import ABD.ABD.PastenBlock.CoeffGCD

namespace ABD

open BigOperators

/-- A divisibility-friendly integer gcd of the `c`-side coefficients.

`CoeffGCD.lean` keeps the normalized natural-number gcd
`cCoeffGCD : ℕ`.  For the first image-divisibility theorem it is convenient to
also use the `Finset.gcd` directly in `ℤ`, because `Finset.gcd_dvd` then gives
integer divisibility of each coefficient without a separate `natAbs` bridge.
A later layer can relate this integer gcd to `(cCoeffGCD : ℤ)`. -/
def ABCTriple.cCoeffIntGCD (T : ABCTriple) : ℤ :=
  (Finset.univ : Finset {p : ℕ // p ∈ T.supportC}).gcd
    (fun hp => T.cCoeff hp)

@[simp]
theorem ABCTriple.cCoeffIntGCD_eq_finset_gcd
    (T : ABCTriple) :
    T.cCoeffIntGCD =
      (Finset.univ : Finset {p : ℕ // p ∈ T.supportC}).gcd
        (fun hp => T.cCoeff hp) := by
  rfl

/-- The integer gcd divides each `c`-side coefficient. -/
theorem ABCTriple.cCoeffIntGCD_dvd_cCoeff
    (T : ABCTriple) (hp : {p : ℕ // p ∈ T.supportC}) :
    T.cCoeffIntGCD ∣ T.cCoeff hp := by
  unfold ABCTriple.cCoeffIntGCD
  exact Finset.gcd_dvd (by simp)

/-- Integer multiples of the divisibility-friendly `c`-coefficient gcd. -/
def ABCTriple.cCoeffIntGCDMultiples (T : ABCTriple) : Set ℤ :=
  {target | T.cCoeffIntGCD ∣ target}

@[simp]
theorem ABCTriple.mem_cCoeffIntGCDMultiples_iff
    (T : ABCTriple) (target : ℤ) :
    target ∈ T.cCoeffIntGCDMultiples ↔ T.cCoeffIntGCD ∣ target := by
  rfl

/-- The integer coefficient gcd divides every `c`-side linear combination. -/
theorem ABCTriple.cCoeffIntGCD_dvd_cLinearForm
    (T : ABCTriple) (xC : T.CTangent) :
    T.cCoeffIntGCD ∣ T.cLinearForm xC := by
  rw [T.cLinearForm_eq_sum]
  refine Finset.dvd_sum ?_
  intro hp _hmem
  exact dvd_mul_of_dvd_left (T.cCoeffIntGCD_dvd_cCoeff hp) (xC hp)

/-- First half of the gcd-image theorem: every element of `cImage` is divisible
by the gcd of the `c`-side coefficients. -/
theorem ABCTriple.cImage_subset_cCoeffIntGCDMultiples
    (T : ABCTriple) :
    T.cImage ⊆ T.cCoeffIntGCDMultiples := by
  intro target htarget
  rw [T.mem_cImage_iff] at htarget
  rcases htarget with ⟨xC, hxC⟩
  rw [T.mem_cCoeffIntGCDMultiples_iff]
  rw [← hxC]
  exact T.cCoeffIntGCD_dvd_cLinearForm xC

/-- The same first-half theorem in pointwise form. -/
theorem ABCTriple.cCoeffIntGCD_dvd_of_mem_cImage
    (T : ABCTriple) {target : ℤ} (htarget : target ∈ T.cImage) :
    T.cCoeffIntGCD ∣ target := by
  exact T.cImage_subset_cCoeffIntGCDMultiples htarget

/-- A `c`-adjustable `a/b` seed has target divisible by the `c`-coefficient gcd.

This is the immediate obstruction half of Theorem 3.  The next layer will prove
the converse using a finite Bezout/linear-combination theorem. -/
theorem ABCTriple.cCoeffIntGCD_dvd_abSeedTarget_of_cAdjustable
    (T : ABCTriple) {xA : T.ATangent} {xB : T.BTangent}
    (hadj : T.CAdjustable xA xB) :
    T.cCoeffIntGCD ∣ T.abSeedTarget xA xB := by
  exact T.cCoeffIntGCD_dvd_of_mem_cImage hadj

end ABD
