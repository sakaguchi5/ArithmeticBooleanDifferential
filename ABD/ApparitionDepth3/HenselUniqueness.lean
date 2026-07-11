/-
  ABD.ApparitionDepth3.HenselUniqueness

  Direct uniqueness inside one simple residue class.  Rather than reconstructing
  correction digits, factor a^d-b^d.  The geometric-sum factor reduces modulo p
  to the unit derivative of the simple seed, hence is already a unit modulo every
  positive power of p.
-/

import ABD.ApparitionDepth3.HenselExistence
import Mathlib.Algebra.Ring.GeomSum

namespace ApparitionDepth3

/-- The geometric factor in a^d-b^d. -/
def powerDifferenceFactor {n : Nat} (a b : ZMod n) (d : Nat) : ZMod n :=
  Finset.sum (Finset.range d) (fun i => a ^ i * b ^ (d - 1 - i))

/-- The standard factorization of a power difference. -/
theorem sub_mul_powerDifferenceFactor
    {n d : Nat} (a b : ZMod n) :
    (a - b) * powerDifferenceFactor a b d = a ^ d - b ^ d := by
  unfold powerDifferenceFactor
  simpa using (Commute.all a b).mul_geom_sum₂ d

/-- Reduction modulo p of the geometric factor over two representatives in the
same seed class is the derivative at the seed. -/
theorem reduce_powerDifferenceFactor_eq_derivative
    {seed a b p d r : Nat}
    (ha : BranchSeedModP seed a p)
    (hb : BranchSeedModP seed b p) :
    ZMod.cast
      (powerDifferenceFactor
        (a : ZMod (p ^ (r + 1)))
        (b : ZMod (p ^ (r + 1))) d) =
      derivativeAt seed p d := by
  have hdiv : p ∣ p ^ (r + 1) := by
    rw [pow_succ]
    exact dvd_mul_left p (p ^ r)
  let red : ZMod (p ^ (r + 1)) →+* ZMod p :=
    ZMod.castHom hdiv (ZMod p)
  change red
      (powerDifferenceFactor
        (a : ZMod (p ^ (r + 1)))
        (b : ZMod (p ^ (r + 1))) d) =
      derivativeAt seed p d
  unfold powerDifferenceFactor
  rw [RingHom.map_geom_sum₂]
  simp only [red, ZMod.castHom_apply, ZMod.cast_natCast hdiv]
  rw [ha, hb]
  simpa [derivativeAt] using
    (geom_sum₂_self (seed : ZMod p) d)

/-- A unit after reduction modulo p is a unit modulo every positive prime power. -/
theorem isUnit_primePower_of_reduction_isUnit
    {p n : Nat} [Fact p.Prime]
    (hn_pos : 0 < n)
    {z : ZMod (p ^ n)}
    (hred : IsUnit (ZMod.cast z : ZMod p)) :
    IsUnit z := by
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hpow_ne : p ^ n ≠ 0 := pow_ne_zero n (Nat.ne_of_gt hp_pos)
  letI : NeZero (p ^ n) := ⟨hpow_ne⟩
  have hrepr : ((z.val : Nat) : ZMod p) = ZMod.cast z := by
    have hz : ((z.val : Nat) : ZMod (p ^ n)) = z := ZMod.natCast_zmod_val z
    have hdiv : p ∣ p ^ n := by
      cases n with
      | zero => exact False.elim ((Nat.not_lt_zero 0) hn_pos)
      | succ k =>
          rw [pow_succ]
          exact dvd_mul_left p (p ^ k)
    have hmap := congrArg (ZMod.castHom hdiv (ZMod p)) hz
    simpa only [ZMod.castHom_apply, ZMod.cast_natCast hdiv] using hmap
  have hnot_dvd : ¬ p ∣ z.val := by
    intro hp_dvd
    have hz0 : ((z.val : Nat) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff z.val p).mpr hp_dvd
    have hred0 : ZMod.cast z = (0 : ZMod p) := by
      rw [← hrepr, hz0]
    exact hred.ne_zero hred0
  have hcop_p_val : Nat.Coprime p z.val :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hnot_dvd
  have hcop_val_pow : Nat.Coprime z.val (p ^ n) :=
    hcop_p_val.symm.pow_right n
  have hcastUnit : IsUnit ((z.val : Nat) : ZMod (p ^ n)) :=
    (ZMod.isUnit_iff_coprime z.val (p ^ n)).mpr hcop_val_pow
  simpa using hcastUnit

/-- Two roots at the same positive prime-power level, lying above the same
simple seed modulo p, are equal at that level. -/
theorem rootAtLevel_unique_in_simpleSeedClass
    {seed a b p d n : Nat} [Fact p.Prime]
    (hn_pos : 0 < n)
    (hsimple : SimpleRootModP seed p d)
    (haSeed : BranchSeedModP seed a p)
    (hbSeed : BranchSeedModP seed b p)
    (haRoot : RootAtLevel a p d n)
    (hbRoot : RootAtLevel b p d n) :
    (a : ZMod (p ^ n)) = (b : ZMod (p ^ n)) := by
  cases n with
  | zero => exact False.elim ((Nat.not_lt_zero 0) hn_pos)
  | succ r =>
      let S : ZMod (p ^ (r + 1)) :=
        powerDifferenceFactor
          (a : ZMod (p ^ (r + 1)))
          (b : ZMod (p ^ (r + 1))) d
      have hredS : ZMod.cast S = derivativeAt seed p d := by
        dsimp [S]
        exact reduce_powerDifferenceFactor_eq_derivative haSeed hbSeed
      have hredUnit : IsUnit (ZMod.cast S : ZMod p) := by
        rw [hredS]
        exact simpleRoot_derivative_unit hsimple
      have hSUnit : IsUnit S :=
        isUnit_primePower_of_reduction_isUnit (Nat.succ_pos r) hredUnit
      have hprod :
          ((a : ZMod (p ^ (r + 1))) - (b : ZMod (p ^ (r + 1)))) * S = 0 := by
        calc
          ((a : ZMod (p ^ (r + 1))) - (b : ZMod (p ^ (r + 1)))) * S =
              (a : ZMod (p ^ (r + 1))) ^ d -
                (b : ZMod (p ^ (r + 1))) ^ d := by
                dsimp [S]
                exact sub_mul_powerDifferenceFactor
                  (a : ZMod (p ^ (r + 1)))
                  (b : ZMod (p ^ (r + 1)))
          _ = 0 := by
            unfold RootAtLevel at haRoot hbRoot
            simpa using congrArg₂ (fun x y => x - y) haRoot hbRoot
      let u : (ZMod (p ^ (r + 1)))ˣ := hSUnit.unit
      have hdiff :
          (a : ZMod (p ^ (r + 1))) - (b : ZMod (p ^ (r + 1))) = 0 := by
        rw [← hSUnit.unit_spec] at hprod
        calc
          (a : ZMod (p ^ (r + 1))) - (b : ZMod (p ^ (r + 1))) =
              ((a : ZMod (p ^ (r + 1))) - (b : ZMod (p ^ (r + 1)))) *
                ((u : ZMod (p ^ (r + 1))) *
                  ((u⁻¹ : (ZMod (p ^ (r + 1)))ˣ) : ZMod (p ^ (r + 1)))) := by simp
          _ = (((a : ZMod (p ^ (r + 1))) - (b : ZMod (p ^ (r + 1)))) *
                (u : ZMod (p ^ (r + 1)))) *
                  ((u⁻¹ : (ZMod (p ^ (r + 1)))ˣ) : ZMod (p ^ (r + 1))) := by
                rw [mul_assoc]
          _ = 0 := by rw [hprod, zero_mul]
      exact sub_eq_zero.mp hdiff

/-- Concrete one-step uniqueness.  In fact the proof establishes the stronger
statement that the simple seed class contains at most one root at level r+1. -/
theorem henselOneStepUnique_of_simpleRoot
    {seed p d : Nat} [Fact p.Prime]
    (hsimple : SimpleRootModP seed p d) :
    HenselOneStepUnique seed p d := by
  intro r hr_pos omega omegaNext₁ omegaNext₂ _hold hnext₁ _hreduce₁ hnext₂ _hreduce₂
  exact rootAtLevel_unique_in_simpleSeedClass
    (n := r + 1) (Nat.succ_pos r) hsimple
    hnext₁.1 hnext₂.1 hnext₁.2 hnext₂.2

end ApparitionDepth3
