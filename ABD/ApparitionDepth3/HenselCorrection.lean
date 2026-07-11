/-
  ABD.ApparitionDepth3.HenselCorrection

  The normalized error and the unique linear correction digit used in one
  finite Hensel step for X^d - 1.
-/

import ABD.ApparitionDepth3.HenselLocal
import Mathlib.Tactic.Ring

namespace ApparitionDepth3

/-- A simple root has a positive exponent.  The case d = 0 would have zero
formal derivative, which cannot be a unit modulo a prime. -/
theorem simpleRoot_exponent_pos
    {seed p d : Nat} [Fact p.Prime]
    (hsimple : SimpleRootModP seed p d) :
    0 < d := by
  apply Nat.pos_of_ne_zero
  intro hd
  subst d
  have hzero : IsUnit (0 : ZMod p) := by
    simpa [derivativeAt] using simpleRoot_derivative_unit hsimple
  exact not_isUnit_zero hzero

/-- A natural representative lying above a simple root modulo a prime is
positive. -/
theorem liftRepresentative_pos_of_simpleRoot
    {seed omega p d r : Nat} [Fact p.Prime]
    (hsimple : SimpleRootModP seed p d)
    (hlift : LiftAtLevel seed omega p d r) :
    0 < omega := by
  apply Nat.pos_of_ne_zero
  intro homega
  subst omega
  have hd_pos : 0 < d := simpleRoot_exponent_pos hsimple
  have hroot := simpleRoot_root hsimple
  unfold RootAtLevel at hroot
  rw [levelOneModulus_eq p] at hroot
  have hseed : (0 : ZMod p) = (seed : ZMod p) := by
    simpa [LiftAtLevel, BranchSeedModP] using hlift.1
  rw [← hseed] at hroot
  have hz : (0 : ZMod p) = 1 := by
    simp [zero_pow (Nat.ne_of_gt hd_pos)] at hroot
  exact zero_ne_one hz

/-- q is the normalized level-r error of omega, read at precision p^(r+1):

    omega^d = 1 + q*p^r  in ZMod (p^(r+1)). -/
def HenselErrorQuotient (omega q p d r : Nat) : Prop :=
  (omega : ZMod (p ^ (r + 1))) ^ d =
    1 + (q : ZMod (p ^ (r + 1))) *
      (p ^ r : ZMod (p ^ (r + 1)))

/-- Every positive natural representative which is a root at level r has a
normalized error quotient at level r+1. -/
theorem exists_errorQuotient_of_rootAtLevel
    {omega p d r : Nat}
    (homega_pos : 0 < omega)
    (hroot : RootAtLevel omega p d r) :
    ∃ q : Nat, HenselErrorQuotient omega q p d r := by
  have hdepth : DepthAtLeast omega p d r :=
    depthAtLeast_of_rootAtLevel_of_base_pos homega_pos hroot
  unfold DepthAtLeast N at hdepth
  let q : Nat := (omega ^ d - 1) / p ^ r
  have hqmul : q * p ^ r = omega ^ d - 1 := by
    dsimp [q]
    exact Nat.div_mul_cancel hdepth
  have hone : 1 ≤ omega ^ d := by
    exact Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero d (Nat.ne_of_gt homega_pos))
  have hnat : omega ^ d = 1 + q * p ^ r := by
    calc
      omega ^ d = (omega ^ d - 1) + 1 := (Nat.sub_add_cancel hone).symm
      _ = q * p ^ r + 1 := by rw [← hqmul]
      _ = 1 + q * p ^ r := Nat.add_comm _ _
  refine ⟨q, ?_⟩
  unfold HenselErrorQuotient
  have hcast := congrArg
    (fun n : Nat => (n : ZMod (p ^ (r + 1)))) hnat
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_mul] using hcast

/-- Quotient existence specialized to a seed-compatible lift of a simple root. -/
theorem exists_errorQuotient_of_lift
    {seed omega p d r : Nat} [Fact p.Prime]
    (hsimple : SimpleRootModP seed p d)
    (hlift : LiftAtLevel seed omega p d r) :
    ∃ q : Nat, HenselErrorQuotient omega q p d r :=
  exists_errorQuotient_of_rootAtLevel
    (liftRepresentative_pos_of_simpleRoot hsimple hlift) hlift.2

/-- The linear equation which kills the normalized error modulo p. -/
def HenselCorrectionEquation (omega q t p d : Nat) : Prop :=
  (q : ZMod p) + (t : ZMod p) * derivativeAt omega p d = 0

/-- A unit derivative solves every Hensel correction equation. -/
theorem exists_correctionDigit_of_derivativeUnit
    {omega q p d : Nat} [NeZero p]
    (hunit : IsUnit (derivativeAt omega p d)) :
    ∃ t : Nat, HenselCorrectionEquation omega q t p d := by
  let u : (ZMod p)ˣ := hunit.unit
  let z : ZMod p := -(q : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p)
  refine ⟨z.val, ?_⟩
  unfold HenselCorrectionEquation
  rw [ZMod.natCast_zmod_val]
  rw [← hunit.unit_spec]
  change (q : ZMod p) + z * (u : ZMod p) = 0
  dsimp [z]
  calc
    (q : ZMod p) +
        (-(q : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p)) * (u : ZMod p)
        = (q : ZMod p) +
            -(q : ZMod p) *
              (((u⁻¹ : (ZMod p)ˣ) : ZMod p) * (u : ZMod p)) := by ring
    _ = 0 := by simp

/-- A unit derivative makes the correction digit unique modulo p. -/
theorem correctionDigit_unique_of_derivativeUnit
    {omega q t₁ t₂ p d : Nat}
    (hunit : IsUnit (derivativeAt omega p d))
    (h₁ : HenselCorrectionEquation omega q t₁ p d)
    (h₂ : HenselCorrectionEquation omega q t₂ p d) :
    (t₁ : ZMod p) = (t₂ : ZMod p) := by
  let u : (ZMod p)ˣ := hunit.unit
  unfold HenselCorrectionEquation at h₁ h₂
  rw [← hunit.unit_spec] at h₁ h₂
  have hmul : (t₁ : ZMod p) * (u : ZMod p) =
      (t₂ : ZMod p) * (u : ZMod p) := by
    apply add_left_cancel (a := (q : ZMod p))
    calc
      (q : ZMod p) + (t₁ : ZMod p) * (u : ZMod p) = 0 := h₁
      _ = (q : ZMod p) + (t₂ : ZMod p) * (u : ZMod p) := h₂.symm
  calc
    (t₁ : ZMod p) =
        (t₁ : ZMod p) * ((u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p)) := by simp
    _ = ((t₁ : ZMod p) * (u : ZMod p)) *
        ((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by rw [mul_assoc]
    _ = ((t₂ : ZMod p) * (u : ZMod p)) *
        ((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by rw [hmul]
    _ = (t₂ : ZMod p) *
        ((u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p)) := by rw [mul_assoc]
    _ = (t₂ : ZMod p) := by simp

end ApparitionDepth3
