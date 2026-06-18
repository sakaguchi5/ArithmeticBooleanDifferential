import Mathlib.Data.Int.GCD
import ABD.ABD.PastenBlock.CImageGCDBezout

namespace ABD

/--
The `ℤ`-valued Finset gcd of integer coefficients agrees with the cast of
    the normalized natural-number gcd of their absolute values.
-/
theorem finset_gcd_int_eq_natAbs_gcd
    {α : Type} (s : Finset α) (f : α → ℤ) :
    s.gcd f = ((s.gcd (fun a => (f a).natAbs) : ℕ) : ℤ) := by
  classical
  refine Finset.induction_on s ?h_empty ?h_insert
  · simp
  · intro a s ha ih
    rw [Finset.gcd_insert, Finset.gcd_insert, ih]
    change (((f a).gcd (((s.gcd (fun x => (f x).natAbs) : ℕ) : ℤ)) : ℕ) : ℤ) =
      ((Nat.gcd (f a).natAbs (s.gcd (fun x => (f x).natAbs)) : ℕ) : ℤ)
    simp [Int.gcd]

/-- The divisibility-friendly integer gcd and the normalized natural gcd are the
same integer after casting the latter to `ℤ`. -/
theorem ABCTriple.cCoeffIntGCD_eq_cCoeffGCD
    (T : ABCTriple) :
    T.cCoeffIntGCD = (T.cCoeffGCD : ℤ) := by
  unfold ABCTriple.cCoeffIntGCD ABCTriple.cCoeffGCD ABCTriple.cCoeffAbs
  exact finset_gcd_int_eq_natAbs_gcd
    (Finset.univ : Finset {p : ℕ // p ∈ T.supportC})
    (fun hp => T.cCoeff hp)

/-- Divisibility by the integer gcd is the same as divisibility by the normalized
natural-number gcd cast to `ℤ`. -/
theorem ABCTriple.cCoeffIntGCD_dvd_iff_cCoeffGCD_dvd
    (T : ABCTriple) (target : ℤ) :
    T.cCoeffIntGCD ∣ target ↔ (T.cCoeffGCD : ℤ) ∣ target := by
  rw [T.cCoeffIntGCD_eq_cCoeffGCD]

/-- Natural-gcd version of the `c`-image divisibility theorem. -/
theorem ABCTriple.mem_cImage_iff_cCoeffGCD_dvd
    (T : ABCTriple) (target : ℤ) :
    target ∈ T.cImage ↔ (T.cCoeffGCD : ℤ) ∣ target := by
  rw [T.mem_cImage_iff_cCoeffIntGCD_dvd]
  rw [T.cCoeffIntGCD_eq_cCoeffGCD]

/-- Set-level equality using the normalized natural-number gcd. -/
theorem ABCTriple.cImage_eq_cCoeffGCDMultiples
    (T : ABCTriple) :
    T.cImage = T.cCoeffGCDMultiples := by
  ext target
  rw [T.mem_cImage_iff_cCoeffGCD_dvd]
  rw [T.mem_cCoeffGCDMultiples_iff]

/-- The `a/b` seed is `c`-adjustable exactly when its target is divisible by the
normalized `c`-coefficient gcd. -/
theorem ABCTriple.cAdjustable_iff_cCoeffGCD_dvd_abSeedTarget
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) :
    T.CAdjustable xA xB ↔ (T.cCoeffGCD : ℤ) ∣ T.abSeedTarget xA xB := by
  unfold ABCTriple.CAdjustable
  rw [T.mem_cImage_iff_cCoeffGCD_dvd]

/-- Divisibility by the normalized `c`-coefficient gcd produces a `c`-side lift. -/
theorem ABCTriple.cAdjustmentLift_of_cCoeffGCD_dvd_abSeedTarget
    (T : ABCTriple) {xA : T.ATangent} {xB : T.BTangent}
    (hdiv : (T.cCoeffGCD : ℤ) ∣ T.abSeedTarget xA xB) :
    Nonempty (T.CAdjustmentLift xA xB) := by
  rw [← T.cAdjustable_iff_nonempty_lift]
  exact (T.cAdjustable_iff_cCoeffGCD_dvd_abSeedTarget xA xB).2 hdiv

end ABD
