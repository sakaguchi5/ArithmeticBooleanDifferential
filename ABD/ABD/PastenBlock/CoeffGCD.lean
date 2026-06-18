import Mathlib.Algebra.GCDMonoid.Finset
import ABD.ABD.PastenBlock.CImageLinear

namespace ABD

/-- Absolute value of a `c`-side derivative coefficient, viewed as a natural
number for gcd purposes. -/
def ABCTriple.cCoeffAbs
    (T : ABCTriple) (hp : {p : ℕ // p ∈ T.supportC}) : ℕ :=
  (T.cCoeff hp).natAbs

/-- The gcd of all `c`-side coefficients.

This is the generator expected for the integer image of
`L_c : ℤ^{S_c} → ℤ`.  The next layer will prove that `cImage` is exactly the set
of integer multiples of this number. -/
def ABCTriple.cCoeffGCD (T : ABCTriple) : ℕ :=
  (Finset.univ : Finset {p : ℕ // p ∈ T.supportC}).gcd
    (fun hp => T.cCoeffAbs hp)

@[simp]
theorem ABCTriple.cCoeffGCD_eq_finset_gcd
    (T : ABCTriple) :
    T.cCoeffGCD =
      (Finset.univ : Finset {p : ℕ // p ∈ T.supportC}).gcd
        (fun hp => T.cCoeffAbs hp) := by
  rfl

/-- The set of integer multiples of the `c`-coefficient gcd. -/
def ABCTriple.cCoeffGCDMultiples (T : ABCTriple) : Set ℤ :=
  {target | (T.cCoeffGCD : ℤ) ∣ target}

@[simp]
theorem ABCTriple.mem_cCoeffGCDMultiples_iff
    (T : ABCTriple) (target : ℤ) :
    target ∈ T.cCoeffGCDMultiples ↔ (T.cCoeffGCD : ℤ) ∣ target := by
  rfl

/-- Each `c`-side coefficient is divisible by the coefficient gcd, at the natural
absolute-value level. -/
theorem ABCTriple.cCoeffGCD_dvd_cCoeffAbs
    (T : ABCTriple) (hp : {p : ℕ // p ∈ T.supportC}) :
    T.cCoeffGCD ∣ T.cCoeffAbs hp := by
  unfold ABCTriple.cCoeffGCD
  exact Finset.gcd_dvd (by simp)

end ABD
