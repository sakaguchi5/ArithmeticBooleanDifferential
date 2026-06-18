import Mathlib.Data.Int.GCD
import Mathlib.Algebra.GCDMonoid.Finset
import ABD.ABD2.Lattice.CoeffGCDBezout

namespace ABD2

open BigOperators

/-- The divisibility-friendly integer gcd of a finite coefficient family.

This uses `Finset.gcd` directly over `ℤ`, matching the old ABD Theorem-3
implementation.  It is deliberately separate from any normalized natural gcd:
for image computations, the important fact is divisibility plus Bezout. -/
def CoeffFinsetGCD {ι : Type*} [Fintype ι] (coeff : ι → ℤ) : ℤ :=
  (Finset.univ : Finset ι).gcd coeff

@[simp]
theorem coeffFinsetGCD_eq_univ_gcd
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) :
    CoeffFinsetGCD coeff = (Finset.univ : Finset ι).gcd coeff := by
  rfl

/-- The finite coefficient gcd divides every coefficient. -/
theorem coeffFinsetGCD_dvd_coeff
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (i : ι) :
    CoeffFinsetGCD coeff ∣ coeff i := by
  unfold CoeffFinsetGCD
  exact Finset.gcd_dvd (by simp)

/-- The finite coefficient gcd as a Step-B common-divisor witness. -/
def coeffFinsetGCDCommonDivisorWitness
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) :
    CoeffGCDCommonDivisorWitness coeff where
  gcd := CoeffFinsetGCD coeff
  commonDivisor := coeffFinsetGCD_dvd_coeff coeff

/-- A coordinate vector, equal to `1` at one index and `0` elsewhere. -/
def singleCoord {ι : Type*} [DecidableEq ι] (i0 : ι) : ι → ℤ :=
  fun i => if i = i0 then 1 else 0

@[simp]
theorem singleCoord_self
    {ι : Type*} [DecidableEq ι] (i0 : ι) :
    singleCoord i0 i0 = 1 := by
  simp [singleCoord]

@[simp]
theorem singleCoord_of_ne
    {ι : Type*} [DecidableEq ι] {i i0 : ι}
    (hne : i ≠ i0) :
    singleCoord i0 i = 0 := by
  simp [singleCoord, hne]

/-- The linear form evaluates a coordinate vector to the corresponding coefficient. -/
theorem integerLinearForm_singleCoord
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coeff : ι → ℤ) (i0 : ι) :
    IntegerLinearForm coeff (singleCoord i0) = coeff i0 := by
  classical
  unfold IntegerLinearForm singleCoord
  simp

/-- Additivity of the finite integer linear form. -/
theorem integerLinearForm_add
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (x y : ι → ℤ) :
    IntegerLinearForm coeff (x + y) =
      IntegerLinearForm coeff x + IntegerLinearForm coeff y := by
  classical
  unfold IntegerLinearForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp [Pi.add_apply, mul_add]

/-- Pull a scalar out of a finite integer linear form. -/
theorem integerLinearForm_mul
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (r : ℤ) (x : ι → ℤ) :
    IntegerLinearForm coeff (fun i => r * x i) =
      r * IntegerLinearForm coeff x := by
  classical
  unfold IntegerLinearForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp [mul_left_comm]

/-- Finite Bezout theorem for a finite subfamily of coefficients.

For any finite set of coordinates, the `Finset.gcd` of the corresponding
coefficients is itself a value of the same integer linear form.  The proof inserts
one coordinate at a time and uses the binary integer Bezout identity supplied by
`Int.gcdA`, `Int.gcdB`, and `Int.gcd_eq_gcd_ab`. -/
theorem exists_integerLinearForm_eq_finset_gcd
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (s : Finset ι) :
    ∃ x : ι → ℤ, IntegerLinearForm coeff x = s.gcd coeff := by
  classical
  refine Finset.induction_on s ?h_empty ?h_insert
  · refine ⟨0, ?_⟩
    unfold IntegerLinearForm
    simp
  · intro a s ha ih
    obtain ⟨xS, hxS⟩ := ih
    let A : ℤ := coeff a
    let G : ℤ := s.gcd coeff
    let u : ℤ := A.gcdA G
    let v : ℤ := A.gcdB G
    refine
      ⟨(fun i => u * singleCoord a i)
          + (fun i => v * xS i), ?_⟩
    have hbez :
        GCDMonoid.gcd A G = A * u + G * v := by
      change ((A.gcd G : ℕ) : ℤ) = A * u + G * v
      simpa [u, v] using Int.gcd_eq_gcd_ab A G
    have hlin :
        IntegerLinearForm coeff
            ((fun i => u * singleCoord a i)
              + (fun i => v * xS i))
          = A * u + G * v := by
      calc
        IntegerLinearForm coeff
            ((fun i => u * singleCoord a i)
              + (fun i => v * xS i))
            =
            IntegerLinearForm coeff (fun i => u * singleCoord a i)
              + IntegerLinearForm coeff (fun i => v * xS i) := by
                rw [integerLinearForm_add]
        _ =
            u * IntegerLinearForm coeff (singleCoord a)
              + v * IntegerLinearForm coeff xS := by
                rw [integerLinearForm_mul]
                rw [integerLinearForm_mul]
        _ =
            u * coeff a + v * G := by
              rw [integerLinearForm_singleCoord]
              rw [hxS]
        _ = A * u + G * v := by
              simp [A, mul_comm]
    calc
      IntegerLinearForm coeff
          ((fun i => u * singleCoord a i)
            + (fun i => v * xS i))
          = A * u + G * v := hlin
      _ = GCDMonoid.gcd A G := hbez.symm
      _ = (insert a s).gcd coeff := by
            symm
            simp [A, G]

/-- The full finite coefficient gcd is a value of the integer linear form. -/
theorem exists_integerLinearForm_eq_coeffFinsetGCD
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) :
    ∃ x : ι → ℤ, IntegerLinearForm coeff x = CoeffFinsetGCD coeff := by
  unfold CoeffFinsetGCD
  exact exists_integerLinearForm_eq_finset_gcd coeff
    (Finset.univ : Finset ι)

/-- The finite coefficient gcd as a Step-C Bezout witness. -/
def coeffFinsetGCDBezoutWitness
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) :
    CoeffGCDBezoutWitness (coeffFinsetGCDCommonDivisorWitness coeff) where
  bezout := exists_integerLinearForm_eq_coeffFinsetGCD coeff

/-- The finite coefficient gcd as a complete image-generator certificate. -/
def coeffFinsetGCDImageGenerator
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) :
    IntegerImageGenerator coeff (CoeffFinsetGCD coeff) :=
  (coeffFinsetGCDCommonDivisorWitness coeff).generatorOfBezout
    (exists_integerLinearForm_eq_coeffFinsetGCD coeff)

/-- Full image theorem for a finite integer linear form and its finite gcd. -/
theorem integerLinearImage_eq_coeffFinsetGCD_multiples
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) :
    IntegerLinearImage coeff = {target : ℤ | CoeffFinsetGCD coeff ∣ target} := by
  exact integerLinearImage_eq_multiples_of_generator coeff
    (coeffFinsetGCDImageGenerator coeff)

/-- Reverse inclusion for the finite gcd image theorem. -/
theorem coeffFinsetGCD_multiples_subset_integerLinearImage
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) :
    {target : ℤ | CoeffFinsetGCD coeff ∣ target} ⊆ IntegerLinearImage coeff := by
  rw [integerLinearImage_eq_coeffFinsetGCD_multiples coeff]

/-- Forward divisibility direction specialized to the finite coefficient gcd. -/
theorem coeffFinsetGCD_dvd_of_mem_integerLinearImage
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) {target : ℤ}
    (htarget : target ∈ IntegerLinearImage coeff) :
    CoeffFinsetGCD coeff ∣ target := by
  have hsubset := integerLinearImage_subset_commonDivisorMultiples coeff
    (coeffFinsetGCD_dvd_coeff coeff)
  exact hsubset htarget

end ABD2
