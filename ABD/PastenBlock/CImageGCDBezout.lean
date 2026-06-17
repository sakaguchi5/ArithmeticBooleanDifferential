import Mathlib.Data.Int.GCD
import ABD.PastenBlock.CImageGCDDivisibility

namespace ABD

open BigOperators

/-- The coordinate tangent that is `1` at one `c`-support coordinate and `0`
elsewhere. -/
def ABCTriple.singleCTangent
    (T : ABCTriple) (hp0 : {p : ℕ // p ∈ T.supportC}) : T.CTangent :=
  fun hp => if hp = hp0 then 1 else 0

@[simp]
theorem ABCTriple.singleCTangent_self
    (T : ABCTriple) (hp0 : {p : ℕ // p ∈ T.supportC}) :
    T.singleCTangent hp0 hp0 = 1 := by
  simp [ABCTriple.singleCTangent]

@[simp]
theorem ABCTriple.singleCTangent_of_ne
    (T : ABCTriple) {hp hp0 : {p : ℕ // p ∈ T.supportC}}
    (hne : hp ≠ hp0) :
    T.singleCTangent hp0 hp = 0 := by
  simp [ABCTriple.singleCTangent, hne]

/-- The `c`-linear form evaluates a coordinate tangent to the corresponding
coefficient. -/
theorem ABCTriple.cLinearForm_singleCTangent
    (T : ABCTriple) (hp0 : {p : ℕ // p ∈ T.supportC}) :
    T.cLinearForm (T.singleCTangent hp0) = T.cCoeff hp0 := by
  classical
  rw [T.cLinearForm_eq_sum]
  simp [ABCTriple.singleCTangent]

theorem ABCTriple.cLinearForm_mul
    (T : ABCTriple) (r : ℤ) (x : T.CTangent) :
    T.cLinearForm (fun hp => r * x hp) =
      r * T.cLinearForm x := by
  classical
  repeat rw [T.cLinearForm_eq_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro hp _hmem
  simp [mul_assoc, mul_comm]

/-- Finite Bezout step for the `c`-coefficient list: the gcd of any finite sublist
of `c`-side coefficients is itself a value of the `c`-linear form.

This is the constructive reverse direction behind Theorem 3.  The proof proceeds
by inserting one coordinate at a time and using the binary Bezout identity for
integers. -/
theorem ABCTriple.exists_cLinearForm_eq_finset_gcd
    (T : ABCTriple) (s : Finset {p : ℕ // p ∈ T.supportC}) :
    ∃ xC : T.CTangent,
      T.cLinearForm xC = s.gcd (fun hp => T.cCoeff hp) := by
  classical
  refine Finset.induction_on s ?h_empty ?h_insert
  · refine ⟨0, ?_⟩
    rw [T.cLinearForm_eq_sum]
    simp
  · intro a s ha ih
    obtain ⟨xS, hxS⟩ := ih
    let A : ℤ := T.cCoeff a
    let G : ℤ := s.gcd (fun hp => T.cCoeff hp)
    let u : ℤ := A.gcdA G
    let v : ℤ := A.gcdB G
    refine
      ⟨(fun hp => u * T.singleCTangent a hp)
          + (fun hp => v * xS hp), ?_⟩
    have hbez :
        GCDMonoid.gcd A G = A * u + G * v := by
      change ((A.gcd G : ℕ) : ℤ) = A * u + G * v
      simpa [u, v] using Int.gcd_eq_gcd_ab A G
    have hlin :
        T.cLinearForm
            ((fun hp => u * T.singleCTangent a hp)
              + (fun hp => v * xS hp))
          = A * u + G * v := by
      calc
        T.cLinearForm
            ((fun hp => u * T.singleCTangent a hp)
              + (fun hp => v * xS hp))
            =
            T.cLinearForm (fun hp => u * T.singleCTangent a hp)
              + T.cLinearForm (fun hp => v * xS hp) := by
                rw [ABCTriple.cLinearForm_add]
        _ =
            u * T.cLinearForm (T.singleCTangent a)
              + v * T.cLinearForm xS := by
                rw [ABCTriple.cLinearForm_mul]
                rw [ABCTriple.cLinearForm_mul]
        _ =
            u * T.cCoeff a + v * G := by
              rw [ABCTriple.cLinearForm_singleCTangent]
              rw [hxS]
        _ = A * u + G * v := by
              simp [A, mul_comm]
    calc
      T.cLinearForm
          ((fun hp => u * T.singleCTangent a hp)
            + (fun hp => v * xS hp))
          = A * u + G * v := hlin
      _ = GCDMonoid.gcd A G := hbez.symm
      _ = (insert a s).gcd (fun hp => T.cCoeff hp) := by
            symm
            simp [A, G]

/-- The integer gcd of all `c`-coefficients is itself in the image of `L_c`. -/
theorem ABCTriple.exists_cLinearForm_eq_cCoeffIntGCD
    (T : ABCTriple) :
    ∃ xC : T.CTangent, T.cLinearForm xC = T.cCoeffIntGCD := by
  unfold ABCTriple.cCoeffIntGCD
  exact T.exists_cLinearForm_eq_finset_gcd
    (Finset.univ : Finset {p : ℕ // p ∈ T.supportC})

/-- The coefficient gcd belongs to the `c`-image. -/
theorem ABCTriple.cCoeffIntGCD_mem_cImage
    (T : ABCTriple) :
    T.cCoeffIntGCD ∈ T.cImage := by
  rw [T.mem_cImage_iff]
  exact T.exists_cLinearForm_eq_cCoeffIntGCD

/-- Every integer multiple of the `c`-coefficient gcd lies in the `c`-image. -/
theorem ABCTriple.mem_cImage_of_cCoeffIntGCD_dvd
    (T : ABCTriple) {target : ℤ} (hdiv : T.cCoeffIntGCD ∣ target) :
    target ∈ T.cImage := by
  rcases hdiv with ⟨k, hk⟩
  rcases T.exists_cLinearForm_eq_cCoeffIntGCD with ⟨xC, hxC⟩
  rw [T.mem_cImage_iff]
  refine ⟨k • xC, ?_⟩
  rw [T.cLinearForm_smul]
  rw [hxC]
  simp [hk,mul_comm]

/-- Second half of the gcd-image theorem: every multiple of the coefficient gcd
is in `cImage`. -/
theorem ABCTriple.cCoeffIntGCDMultiples_subset_cImage
    (T : ABCTriple) :
    T.cCoeffIntGCDMultiples ⊆ T.cImage := by
  intro target htarget
  rw [T.mem_cCoeffIntGCDMultiples_iff] at htarget
  exact T.mem_cImage_of_cCoeffIntGCD_dvd htarget

/-- Full integer-gcd image theorem for the `c`-side adjustment map. -/
theorem ABCTriple.mem_cImage_iff_cCoeffIntGCD_dvd
    (T : ABCTriple) (target : ℤ) :
    target ∈ T.cImage ↔ T.cCoeffIntGCD ∣ target := by
  constructor
  · intro htarget
    exact T.cCoeffIntGCD_dvd_of_mem_cImage htarget
  · intro hdiv
    exact T.mem_cImage_of_cCoeffIntGCD_dvd hdiv

/-- Set-level equality form of the integer-gcd image theorem. -/
theorem ABCTriple.cImage_eq_cCoeffIntGCDMultiples
    (T : ABCTriple) :
    T.cImage = T.cCoeffIntGCDMultiples := by
  ext target
  rw [T.mem_cImage_iff_cCoeffIntGCD_dvd]
  rw [T.mem_cCoeffIntGCDMultiples_iff]

/-- The `a/b` seed is `c`-adjustable exactly when its target is divisible by the
`c`-coefficient gcd. -/
theorem ABCTriple.cAdjustable_iff_cCoeffIntGCD_dvd_abSeedTarget
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) :
    T.CAdjustable xA xB ↔ T.cCoeffIntGCD ∣ T.abSeedTarget xA xB := by
  unfold ABCTriple.CAdjustable
  rw [T.mem_cImage_iff_cCoeffIntGCD_dvd]

/-- Reverse adjustment theorem: divisibility by the `c`-coefficient gcd produces
a `c`-side lift. -/
theorem ABCTriple.cAdjustmentLift_of_cCoeffIntGCD_dvd_abSeedTarget
    (T : ABCTriple) {xA : T.ATangent} {xB : T.BTangent}
    (hdiv : T.cCoeffIntGCD ∣ T.abSeedTarget xA xB) :
    Nonempty (T.CAdjustmentLift xA xB) := by
  rw [← T.cAdjustable_iff_nonempty_lift]
  exact (T.cAdjustable_iff_cCoeffIntGCD_dvd_abSeedTarget xA xB).2 hdiv

end ABD
