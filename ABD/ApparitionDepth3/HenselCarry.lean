/-
  ABD.ApparitionDepth3.HenselCarry

  Canonical normalized error, the unique next correction digit, and the
  zero-carry criterion for a finite Hensel representative.
-/

import ABD.ApparitionDepth3.CyclotomicDepth

namespace ApparitionDepth3

/-- The canonical normalized integer error at level r. -/
def henselErrorNat (omega p d r : Nat) : Nat :=
  (omega ^ d - 1) / p ^ r

/-- The next error digit, read modulo p. -/
def HenselErrorDigit (omega p d r : Nat) : ZMod p :=
  (henselErrorNat omega p d r : ZMod p)

/-- The unique correction digit determined by a unit derivative. -/
noncomputable def HenselCorrectionDigit
    (omega p d r : Nat)
    (hunit : IsUnit (derivativeAt omega p d)) : ZMod p :=
  -(HenselErrorDigit omega p d r) *
    (((hunit.unit)⁻¹ : (ZMod p)ˣ) : ZMod p)

/-- The natural representative in [0,p) of the canonical correction digit. -/
noncomputable def HenselCorrectionDigitNat
    (omega p d r : Nat)
    (hunit : IsUnit (derivativeAt omega p d)) : Nat :=
  (HenselCorrectionDigit omega p d r hunit).val

/-- The canonical quotient really represents the level-r error at precision
p^(r+1). -/
theorem canonical_henselErrorQuotient
    {omega p d r : Nat}
    (homegaPos : 0 < omega)
    (hroot : RootAtLevel omega p d r) :
    HenselErrorQuotient omega (henselErrorNat omega p d r) p d r := by
  have hdepth : DepthAtLeast omega p d r :=
    depthAtLeast_of_rootAtLevel_of_base_pos homegaPos hroot
  unfold DepthAtLeast N at hdepth
  have hmul : henselErrorNat omega p d r * p ^ r = omega ^ d - 1 := by
    unfold henselErrorNat
    exact Nat.div_mul_cancel hdepth
  have hone : 1 ≤ omega ^ d :=
    Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero d (Nat.ne_of_gt homegaPos))
  have hnat :
      omega ^ d = 1 + henselErrorNat omega p d r * p ^ r := by
    calc
      omega ^ d = (omega ^ d - 1) + 1 := (Nat.sub_add_cancel hone).symm
      _ = henselErrorNat omega p d r * p ^ r + 1 := by rw [← hmul]
      _ = 1 + henselErrorNat omega p d r * p ^ r := Nat.add_comm _ _
  unfold HenselErrorQuotient
  have hcast := congrArg
    (fun n : Nat => (n : ZMod (p ^ (r + 1)))) hnat
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_mul] using hcast

/-- The canonical digit solves the linear Hensel correction equation. -/
theorem canonicalCorrectionEquation
    {omega p d r : Nat} [NeZero p]
    (hunit : IsUnit (derivativeAt omega p d)) :
    HenselCorrectionEquation omega (henselErrorNat omega p d r)
      (HenselCorrectionDigitNat omega p d r hunit) p d := by
  let u : (ZMod p)ˣ := hunit.unit
  unfold HenselCorrectionEquation HenselCorrectionDigitNat
  rw [ZMod.natCast_zmod_val]
  rw [← hunit.unit_spec]
  change HenselErrorDigit omega p d r +
      HenselCorrectionDigit omega p d r hunit * (u : ZMod p) = 0
  unfold HenselCorrectionDigit
  change HenselErrorDigit omega p d r +
      (-HenselErrorDigit omega p d r *
        (((u⁻¹ : (ZMod p)ˣ) : ZMod p))) * (u : ZMod p) = 0
  calc
    HenselErrorDigit omega p d r +
        (-HenselErrorDigit omega p d r *
          (((u⁻¹ : (ZMod p)ˣ) : ZMod p))) * (u : ZMod p) =
      HenselErrorDigit omega p d r +
        -HenselErrorDigit omega p d r *
          ((((u⁻¹ : (ZMod p)ˣ) : ZMod p)) * (u : ZMod p)) := by ring
    _ = 0 := by simp

/-- The first-order formula before imposing the correction equation. -/
theorem correctedRepresentative_errorFormula
    {omega q t p d r : Nat}
    (hrPos : 0 < r)
    (hquot : HenselErrorQuotient omega q p d r) :
    (correctedRepresentative omega t p r : ZMod (p ^ (r + 1))) ^ d =
      1 + ((q + t * derivativeNat omega d : Nat) : ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1))) := by
  calc
    (correctedRepresentative omega t p r : ZMod (p ^ (r + 1))) ^ d =
        (omega : ZMod (p ^ (r + 1))) ^ d +
          ((t : ZMod (p ^ (r + 1))) *
            (p ^ r : ZMod (p ^ (r + 1)))) *
              ((d : ZMod (p ^ (r + 1))) *
                (omega : ZMod (p ^ (r + 1))) ^ (d - 1)) :=
      correctedRepresentative_firstOrder omega t p d r hrPos
    _ = (1 + (q : ZMod (p ^ (r + 1))) *
          (p ^ r : ZMod (p ^ (r + 1)))) +
          ((t : ZMod (p ^ (r + 1))) *
            (p ^ r : ZMod (p ^ (r + 1)))) *
              ((d : ZMod (p ^ (r + 1))) *
                (omega : ZMod (p ^ (r + 1))) ^ (d - 1)) := by rw [hquot]
    _ = 1 + ((q + t * derivativeNat omega d : Nat) :
          ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1))) := by
      simp only [derivativeNat, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      ring

/-- Cancelling p^r from a zero at precision p^(r+1) leaves a zero modulo p. -/
theorem modP_eq_zero_of_mul_henselPower_eq_zero
    {a p r : Nat} [Fact p.Prime]
    (hzero :
      (a : ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1))) = 0) :
    (a : ZMod p) = 0 := by
  have hdvd : p ^ (r + 1) ∣ a * p ^ r := by
    rw [← ZMod.natCast_eq_zero_iff]
    simpa only [Nat.cast_mul, Nat.cast_pow] using hzero
  rcases hdvd with ⟨k, hk⟩
  have hpPowPos : 0 < p ^ r := pow_pos (Fact.out : Nat.Prime p).pos r
  have hEq : a * p ^ r = (p * k) * p ^ r := by
    calc
      a * p ^ r = p ^ (r + 1) * k := hk
      _ = (p * k) * p ^ r := by
        rw [pow_succ]
        ring
  have ha : a = p * k := Nat.eq_of_mul_eq_mul_right hpPowPos hEq
  exact (ZMod.natCast_eq_zero_iff a p).mpr ⟨k, ha⟩

/-- A candidate next digit gives a root exactly when it solves the correction
equation. -/
theorem rootAtNextLevel_iff_correctionEquation
    {omega q t p d r : Nat} [Fact p.Prime]
    (hrPos : 0 < r)
    (hquot : HenselErrorQuotient omega q p d r) :
    RootAtLevel (correctedRepresentative omega t p r) p d (r + 1) ↔
      HenselCorrectionEquation omega q t p d := by
  constructor
  · intro hroot
    have hformula := correctedRepresentative_errorFormula (t := t) hrPos hquot
    unfold RootAtLevel at hroot
    have hmul :
        ((q + t * derivativeNat omega d : Nat) : ZMod (p ^ (r + 1))) *
          (p ^ r : ZMod (p ^ (r + 1))) = 0 := by
      apply add_left_cancel (a := (1 : ZMod (p ^ (r + 1))))
      simpa [hroot] using hformula.symm
    have hmod := modP_eq_zero_of_mul_henselPower_eq_zero hmul
    simpa [HenselCorrectionEquation, derivativeAt, derivativeNat,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hmod
  · intro hcorr
    exact rootAtNextLevel_of_quotient_correction hrPos hquot hcorr

/-- The canonical corrected representative is the next root. -/
theorem canonicalCorrectedRepresentative_root
    {seed omega p d r : Nat} [Fact p.Prime]
    (hsimple : SimpleRootModP seed p d)
    (hrPos : 0 < r)
    (hlift : LiftAtLevel seed omega p d r) :
    RootAtLevel
      (correctedRepresentative omega
        (HenselCorrectionDigitNat omega p d r
          (derivativeUnit_of_seedCongr hsimple hlift.1)) p r)
      p d (r + 1) := by
  have homegaPos := liftRepresentative_pos_of_simpleRoot hsimple hlift
  have hquot := canonical_henselErrorQuotient homegaPos hlift.2
  have hunit := derivativeUnit_of_seedCongr hsimple hlift.1
  exact (rootAtNextLevel_iff_correctionEquation hrPos hquot).mpr
    (canonicalCorrectionEquation hunit)

/-- The next digit is unique modulo p. -/
theorem rootAtNextLevel_iff_digit_eq_canonical
    {seed omega t p d r : Nat} [Fact p.Prime]
    (hsimple : SimpleRootModP seed p d)
    (hrPos : 0 < r)
    (hlift : LiftAtLevel seed omega p d r) :
    RootAtLevel (correctedRepresentative omega t p r) p d (r + 1) ↔
      (t : ZMod p) =
        HenselCorrectionDigit omega p d r
          (derivativeUnit_of_seedCongr hsimple hlift.1) := by
  let hunit : IsUnit (derivativeAt omega p d) :=
    derivativeUnit_of_seedCongr hsimple hlift.1
  have homegaPos := liftRepresentative_pos_of_simpleRoot hsimple hlift
  have hquot := canonical_henselErrorQuotient homegaPos hlift.2
  have hcanonical :
      HenselCorrectionEquation omega (henselErrorNat omega p d r)
        (HenselCorrectionDigitNat omega p d r hunit) p d :=
    canonicalCorrectionEquation hunit
  have hcastCanonical :
      ((HenselCorrectionDigitNat omega p d r hunit : Nat) : ZMod p) =
        HenselCorrectionDigit omega p d r hunit := by
    unfold HenselCorrectionDigitNat
    exact ZMod.natCast_zmod_val _
  constructor
  · intro hroot
    have htEq : HenselCorrectionEquation omega (henselErrorNat omega p d r) t p d :=
      (rootAtNextLevel_iff_correctionEquation hrPos hquot).mp hroot
    have huniq := correctionDigit_unique_of_derivativeUnit hunit htEq hcanonical
    exact huniq.trans hcastCanonical
  · intro ht
    apply (rootAtNextLevel_iff_correctionEquation hrPos hquot).mpr
    unfold HenselCorrectionEquation at hcanonical ⊢
    rw [ht, ← hcastCanonical]
    exact hcanonical

/-- Zero error digit is exactly the condition that the current representative
already survives one more level without changing its next p-adic digit. -/
theorem rootAtNextLevel_iff_errorDigit_zero
    {seed omega p d r : Nat} [Fact p.Prime]
    (hsimple : SimpleRootModP seed p d)
    (hrPos : 0 < r)
    (hlift : LiftAtLevel seed omega p d r) :
    RootAtLevel omega p d (r + 1) ↔
      HenselErrorDigit omega p d r = 0 := by
  have homegaPos := liftRepresentative_pos_of_simpleRoot hsimple hlift
  have hquot := canonical_henselErrorQuotient homegaPos hlift.2
  have hiff := rootAtNextLevel_iff_correctionEquation
    (omega := omega) (q := henselErrorNat omega p d r)
    (t := 0) hrPos hquot
  simpa [correctedRepresentative, HenselCorrectionEquation,
    HenselErrorDigit] using hiff

/--
The Nat-valued representatives in `HenselCorrectionEquation`
recover the corresponding canonical `ZMod p` digits.
-/
theorem canonicalCorrectionEquation_digit_form
    {omega p d r : Nat} [NeZero p]
    (hunit : IsUnit (derivativeAt omega p d)) :
    HenselErrorDigit omega p d r +
        HenselCorrectionDigit omega p d r hunit *
          derivativeAt omega p d =
      0 := by
  have hEq :=
    canonicalCorrectionEquation
      (omega := omega) (r := r) hunit
  unfold HenselCorrectionEquation at hEq
  simpa only [
    henselErrorNat,
    HenselErrorDigit,
    HenselCorrectionDigitNat,
    ZMod.natCast_zmod_val
  ] using hEq

/-- The canonical correction digit vanishes exactly when the error digit does. -/
theorem correctionDigit_eq_zero_iff_errorDigit_eq_zero
    {omega p d r : Nat} [NeZero p]
    (hunit : IsUnit (derivativeAt omega p d)) :
    HenselCorrectionDigit omega p d r hunit = 0 ↔
      HenselErrorDigit omega p d r = 0 := by
  constructor
  · intro hcorrZero
    have hEq :=
      canonicalCorrectionEquation_digit_form
        (omega := omega) (r := r) hunit
    rw [hcorrZero, zero_mul, add_zero] at hEq
    exact hEq
  · intro herrZero
    unfold HenselCorrectionDigit
    rw [herrZero, neg_zero, zero_mul]

/-- Zero-carry criterion in correction-digit form. -/
theorem rootAtNextLevel_iff_correctionDigit_zero
    {seed omega p d r : Nat} [Fact p.Prime]
    (hsimple : SimpleRootModP seed p d)
    (hrPos : 0 < r)
    (hlift : LiftAtLevel seed omega p d r) :
    RootAtLevel omega p d (r + 1) ↔
      HenselCorrectionDigit omega p d r
        (derivativeUnit_of_seedCongr hsimple hlift.1) = 0 := by
  rw [rootAtNextLevel_iff_errorDigit_zero hsimple hrPos hlift]
  exact (correctionDigit_eq_zero_iff_errorDigit_eq_zero
    (derivativeUnit_of_seedCongr hsimple hlift.1)).symm

end ApparitionDepth3
