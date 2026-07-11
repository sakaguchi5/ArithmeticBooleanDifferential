/-
  ABD.ApparitionDepth3.WittPadicRoot

  Stage 10, first half:
    * the Witt-vector Teichmuller root attached to a concrete branch seed;
    * its image in the p-adic integers;
    * compatible finite reductions modulo p^r.
-/

import ABD.ApparitionDepth3.FiniteSynthesis
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.WittVector.Compare

namespace ApparitionDepth3

open scoped Witt

/-- The residue-class root selected by the concrete `(g,p,d,j)` branch. -/
def branchResidue (g p d j : Nat) : ZMod p :=
  (branchSeed g p d j : ZMod p)

/-- The canonical Witt-vector Teichmuller root of the branch residue. -/
noncomputable def branchWittRoot
    (g p d j : Nat) [Fact p.Prime] : WittVector p (ZMod p) :=
  WittVector.teichmuller p (branchResidue g p d j)

/-- The corresponding p-adic integer under the standard Witt/p-adic equivalence. -/
noncomputable def branchPadicRoot
    (g p d j : Nat) [Fact p.Prime] : ℤ_[p] :=
  WittVector.equiv p (branchWittRoot g p d j)

/-- Reduction of the branch p-adic root modulo `p^r`. -/
noncomputable def branchPadicReduction
    (g p d j r : Nat) [Fact p.Prime] : ZMod (p ^ r) :=
  PadicInt.toZModPow r (branchPadicRoot g p d j)

/-- The Witt root is a genuine d-th root of unity. -/
theorem branchWittRoot_pow_eq_one
    {g p d j : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j) :
    (branchWittRoot g p d j) ^ d = 1 := by
  have hseed := branchSeed_rootAtLevel_one hcopG hprimitive hparams
  unfold RootAtLevel at hseed
  rw [levelOneModulus_eq p] at hseed
  unfold branchWittRoot branchResidue
  rw [← map_pow, hseed, map_one]

/-- The p-adic image of the Witt root is a d-th root of unity. -/
theorem branchPadicRoot_pow_eq_one
    {g p d j : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j) :
    (branchPadicRoot g p d j) ^ d = 1 := by
  unfold branchPadicRoot
  rw [← map_pow, branchWittRoot_pow_eq_one hcopG hprimitive hparams, map_one]

/-- Every finite reduction of the p-adic root is a d-th root of unity. -/
theorem branchPadicReduction_pow_eq_one
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j) :
    (branchPadicReduction g p d j r) ^ d = 1 := by
  unfold branchPadicReduction
  rw [← map_pow, branchPadicRoot_pow_eq_one hcopG hprimitive hparams, map_one]

/-- The finite reductions form a compatible inverse system. -/
theorem branchPadicReduction_compat
    {g p d j m n : Nat} [Fact p.Prime]
    (hmn : m ≤ n) :
    ZMod.cast (branchPadicReduction g p d j n) =
      branchPadicReduction g p d j m := by
  unfold branchPadicReduction
  exact PadicInt.cast_toZModPow m n hmn (branchPadicRoot g p d j)

/-- The zero-th Witt coefficient of a natural-number cast is its residue.
This small local lemma makes the level-one comparison independent of any
special-purpose simp theorem for Witt-vector natural casts. -/
private theorem truncatedWitt_natCast_coeff_zero
    (p n : Nat) [Fact p.Prime] :
    ((n : TruncatedWittVector p 1 (ZMod p))).coeff (0 : Fin 1) =
      (n : ZMod p) := by
  change ((n : WittVector p (ZMod p))).coeff 0 = (n : ZMod p)
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ,
        WittVector.add_coeff_zero,
        ih,
        WittVector.one_coeff_zero,
        Nat.cast_succ]

private theorem RingEquiv.apply_symm_toRingHom_apply
    {R S : Type*} [Semiring R] [Semiring S]
    (e : R ≃+* S) (x : S) :
    e (e.symm.toRingHom x) = x := by
  exact RingEquiv.apply_symm_apply e x

/-- At level one, the Witt inverse-limit coordinate is exactly the selected
branch residue. -/
theorem branchWittRoot_toZModPow_one
    {g p d j : Nat} [Fact p.Prime] :
    WittVector.toZModPow p 1 (branchWittRoot g p d j) =
      (branchSeed g p d j : ZMod (p ^ 1)) := by
  apply (TruncatedWittVector.zmodEquivTrunc p 1).injective
  simp only [WittVector.toZModPow, RingHom.comp_apply,
    RingEquiv.apply_symm_toRingHom_apply]
  rw [map_natCast]
  apply TruncatedWittVector.ext
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  change
    (WittVector.truncateFun 1 (branchWittRoot g p d j)).coeff (0 : Fin 1) =
      ((branchSeed g p d j : TruncatedWittVector p 1 (ZMod p))).coeff
        (0 : Fin 1)
  rw [WittVector.coeff_truncateFun]
  unfold branchWittRoot branchResidue
  change
    ((WittVector.teichmuller p) (branchSeed g p d j : ZMod p)).coeff (0 : ℕ) =
      _
  rw [WittVector.teichmuller_coeff_zero]
  symm
  exact truncatedWitt_natCast_coeff_zero p (branchSeed g p d j)

/-- The p-adic reduction agrees with the finite coordinate used to construct
`WittVector.equiv`. -/
theorem branchPadicReduction_eq_wittToZModPow
    {g p d j r : Nat} [Fact p.Prime] :
    branchPadicReduction g p d j r =
      WittVector.toZModPow p r (branchWittRoot g p d j) := by
  unfold branchPadicReduction branchPadicRoot
  change
    PadicInt.toZModPow r
        (WittVector.toPadicInt p (branchWittRoot g p d j)) = _
  rw [WittVector.toPadicInt]
  rw [← RingHom.comp_apply]
  rw [PadicInt.lift_spec]

/-- Reduction modulo p recovers the concrete branch seed. -/
theorem branchPadicReduction_one
    {g p d j : Nat} [Fact p.Prime] :
    branchPadicReduction g p d j 1 =
      (branchSeed g p d j : ZMod (p ^ 1)) := by
  rw [branchPadicReduction_eq_wittToZModPow]
  exact branchWittRoot_toZModPow_one

/-- Every positive finite reduction lies above the original branch seed modulo p. -/
theorem branchPadicReduction_modP
    {g p d j r : Nat} [Fact p.Prime]
    (hrPos : 0 < r) :
    (ZMod.cast (branchPadicReduction g p d j r) : ZMod p) =
      (branchSeed g p d j : ZMod p) := by
  have hrOne : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hrPos.ne'
  have hcompat :=
    branchPadicReduction_compat
      (g := g) (p := p) (d := d) (j := j) hrOne
  rw [branchPadicReduction_one] at hcompat
  let e : ZMod (p ^ 1) ≃+* ZMod p :=
    ZMod.ringEquivCongr (pow_one p)
  have htransport :
      e (ZMod.cast (branchPadicReduction g p d j r) : ZMod (p ^ 1)) =
        e (branchSeed g p d j : ZMod (p ^ 1)) :=
    congrArg e hcompat
  simpa only [ZMod.cast_eq_val, map_natCast] using htransport

end ApparitionDepth3
