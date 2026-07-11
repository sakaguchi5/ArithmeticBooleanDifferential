/-
  ABD.ApparitionDepth3.HenselExpansion

  The first-order expansion modulo p^(r+1) and the proof that the correction
  equation kills the normalized level-r error.
-/

import ABD.ApparitionDepth3.HenselCorrection

namespace ApparitionDepth3

/-- The underlying natural derivative value d*omega^(d-1). -/
def derivativeNat (omega d : Nat) : Nat :=
  d * omega ^ (d - 1)

/-- The corrected natural representative in one finite Hensel step. -/
def correctedRepresentative (omega t p r : Nat) : Nat :=
  omega + t * p ^ r

lemma pow_square_eq_pow_mul_two (p r : Nat) :
    p ^ r * p ^ r = p ^ (r * 2) := by
  rw [Nat.mul_two]
  rw [pow_add]

lemma pow_mul_two_eq_pow_square (p r : Nat) :
    p ^ (r * 2) = p ^ r * p ^ r := by
  rw [Nat.mul_two, pow_add]

lemma cast_pow_symm {R} [Semiring R] (n k : Nat) :
    (n : R) ^ k = ((n ^ k : Nat) : R) := by
  symm
  exact Nat.cast_pow n k

/-- The corrected representative reduces to the old one modulo p^r. -/
theorem correctedRepresentative_reduce
    (omega t p r : Nat) :
    (correctedRepresentative omega t p r : ZMod (p ^ r)) =
      (omega : ZMod (p ^ r)) := by
  unfold correctedRepresentative
  simp only [Nat.cast_add, Nat.cast_mul]
  rw [ZMod.natCast_self]
  simp

/-- At a positive level the correction term is already zero modulo p, so the
corrected representative stays above the same seed. -/
theorem correctedRepresentative_seedCongr
    {seed omega t p r : Nat}
    (hr_pos : 0 < r)
    (hseed : BranchSeedModP seed omega p) :
    BranchSeedModP seed (correctedRepresentative omega t p r) p := by
  unfold BranchSeedModP correctedRepresentative
  cases r with
  | zero => exact False.elim ((Nat.not_lt_zero 0) hr_pos)
    | succ k =>
      simpa [BranchSeedModP] using hseed

/-- Square-zero first-order power expansion in any commutative semiring. -/
theorem squareZero_firstOrderPower_succ
    {R : Type*} [CommSemiring R]
    {x y : R} (hy : y * y = 0) :
    ∀ n : Nat,
      (x + y) ^ (Nat.succ n) =
        x ^ (Nat.succ n) +
          y * (((Nat.succ n : Nat) : R) * x ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (x + y) ^ (Nat.succ (Nat.succ n)) =
            (x + y) ^ (Nat.succ n) * (x + y) := by rw [pow_succ]
        _ = (x ^ (Nat.succ n) +
              y * (((Nat.succ n : Nat) : R) * x ^ n)) * (x + y) := by
              rw [ih]
        _ = x ^ (Nat.succ (Nat.succ n)) +
              y * (((Nat.succ (Nat.succ n) : Nat) : R) *
                x ^ (Nat.succ n)) := by
              have hy_pow : y ^ 2 = 0 := by simpa [pow_two] using hy
              ring_nf
              simp [hy_pow]
              ring_nf

/-- Square-zero first-order power expansion, including exponent zero. -/
theorem squareZero_firstOrderPower
    {R : Type*} [CommSemiring R]
    {x y : R} (hy : y * y = 0) (d : Nat) :
    (x + y) ^ d =
      x ^ d + y * ((d : R) * x ^ (d - 1)) := by
  cases d with
  | zero => simp
  | succ n =>
      simpa using squareZero_firstOrderPower_succ (R := R) (x := x) (y := y) hy n

/-- The factor p^r is square-zero in ZMod (p^(r+1)) for every positive r. -/
theorem henselPower_squareZero
    (p r : Nat) (hr_pos : 0 < r) :
    (p ^ r : ZMod (p ^ (r + 1))) *
      (p ^ r : ZMod (p ^ (r + 1))) = 0 := by
  rw [← Nat.cast_pow]
  rw [← Nat.cast_mul]
  rw [ZMod.natCast_eq_zero_iff]
  have hle : r + 1 ≤ r * 2 := by
    have hr_one : 1 ≤ r := Nat.succ_le_of_lt hr_pos
    calc
      r + 1 ≤ r + r := Nat.add_le_add_left hr_one r
      _ = r * 2 := by simp [Nat.mul_two]
  have hpow : p ^ (r + 1) ∣ p ^ (r * 2) := pow_dvd_pow p hle
  simpa [Nat.mul_two, pow_add] using hpow

/-- The full correction term t*p^r is square-zero at the next precision. -/
theorem correctionTerm_squareZero
    (t p r : Nat) (hr_pos : 0 < r) :
    ((t : ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1)))) *
      ((t : ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1)))) = 0 := by
  have hbase := henselPower_squareZero p r hr_pos
  calc
    ((t : ZMod (p ^ (r + 1))) * (p ^ r : ZMod (p ^ (r + 1)))) *
        ((t : ZMod (p ^ (r + 1))) * (p ^ r : ZMod (p ^ (r + 1)))) =
      ((t : ZMod (p ^ (r + 1))) * (t : ZMod (p ^ (r + 1)))) *
        ((p ^ r : ZMod (p ^ (r + 1))) *
          (p ^ r : ZMod (p ^ (r + 1)))) := by ring
    _ = 0 := by rw [hbase, mul_zero]

/-- The corrected representative satisfies the first-order power formula at
precision p^(r+1). -/
theorem correctedRepresentative_firstOrder
    (omega t p d r : Nat) (hr_pos : 0 < r) :
    (correctedRepresentative omega t p r : ZMod (p ^ (r + 1))) ^ d =
      (omega : ZMod (p ^ (r + 1))) ^ d +
        ((t : ZMod (p ^ (r + 1))) *
          (p ^ r : ZMod (p ^ (r + 1)))) *
            ((d : ZMod (p ^ (r + 1))) *
              (omega : ZMod (p ^ (r + 1))) ^ (d - 1)) := by
  have hy := correctionTerm_squareZero t p r hr_pos
  simpa [correctedRepresentative, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using
    (squareZero_firstOrderPower
      (R := ZMod (p ^ (r + 1)))
      (x := (omega : ZMod (p ^ (r + 1))))
      (y := (t : ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1)))) hy d)

/-- The correction equation is equivalently a natural expression vanishing
modulo p. -/
theorem correctionEquation_natCast_eq_zero
    {omega q t p d : Nat}
    (hcorr : HenselCorrectionEquation omega q t p d) :
    ((q + t * derivativeNat omega d : Nat) : ZMod p) = 0 := by
  simpa [HenselCorrectionEquation, derivativeAt, derivativeNat,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hcorr

/-- A natural number which is zero modulo p becomes zero at precision p^(r+1)
after multiplication by p^r. -/
theorem cast_mul_henselPower_eq_zero_of_modP
    {a p r : Nat}
    (ha : (a : ZMod p) = 0) :
    (a : ZMod (p ^ (r + 1))) *
      (p ^ r : ZMod (p ^ (r + 1))) = 0 := by
  have hp_dvd : p ∣ a := (ZMod.natCast_eq_zero_iff a p).mp ha
  rcases hp_dvd with ⟨k, rfl⟩
  rw [← Nat.cast_pow]
  rw [← Nat.cast_mul]
  rw [ZMod.natCast_eq_zero_iff]
  use k
  ring

/-- Quotient plus a solved correction equation produces a root at the next
precision. -/
theorem rootAtNextLevel_of_quotient_correction
    {omega q t p d r : Nat}
    (hr_pos : 0 < r)
    (hquot : HenselErrorQuotient omega q p d r)
    (hcorr : HenselCorrectionEquation omega q t p d) :
    RootAtLevel (correctedRepresentative omega t p r) p d (r + 1) := by
  have hcorrNat := correctionEquation_natCast_eq_zero hcorr
  have hkill :
      ((q + t * derivativeNat omega d : Nat) : ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1))) = 0 :=
    cast_mul_henselPower_eq_zero_of_modP hcorrNat
  unfold RootAtLevel
  unfold HenselErrorQuotient at hquot
  calc
    (correctedRepresentative omega t p r : ZMod (p ^ (r + 1))) ^ d =
        (omega : ZMod (p ^ (r + 1))) ^ d +
          ((t : ZMod (p ^ (r + 1))) *
            (p ^ r : ZMod (p ^ (r + 1)))) *
              ((d : ZMod (p ^ (r + 1))) *
                (omega : ZMod (p ^ (r + 1))) ^ (d - 1)) :=
      correctedRepresentative_firstOrder omega t p d r hr_pos
    _ = (1 + (q : ZMod (p ^ (r + 1))) *
          (p ^ r : ZMod (p ^ (r + 1)))) +
          ((t : ZMod (p ^ (r + 1))) *
            (p ^ r : ZMod (p ^ (r + 1)))) *
              ((d : ZMod (p ^ (r + 1))) *
                (omega : ZMod (p ^ (r + 1))) ^ (d - 1)) := by rw [hquot]
    _ = 1 +
        ((q + t * derivativeNat omega d : Nat) : ZMod (p ^ (r + 1))) *
          (p ^ r : ZMod (p ^ (r + 1))) := by
      simp only [derivativeNat, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      ring
    _ = 1 := by rw [hkill, add_zero]

end ApparitionDepth3
