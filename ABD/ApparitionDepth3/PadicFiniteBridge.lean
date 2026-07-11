/-
  ABD.ApparitionDepth3.PadicFiniteBridge

  Stage 10, second half:
    * a canonical natural representative of every p-adic reduction;
    * proof that it is a finite Hensel/Teichmuller lift;
    * identification with every previously generated finite lift by uniqueness.
-/

import ABD.ApparitionDepth3.WittPadicRoot

namespace ApparitionDepth3

/-- The standard natural representative of the p-adic reduction modulo `p^r`. -/
noncomputable def branchPadicRepresentative
    (g p d j r : Nat) [Fact p.Prime] : Nat :=
  (branchPadicReduction g p d j r).val

/-- Casting the standard representative back into `ZMod (p^r)` recovers the
p-adic reduction. -/
theorem branchPadicRepresentative_cast
    {g p d j r : Nat} [Fact p.Prime] :
    (branchPadicRepresentative g p d j r : ZMod (p ^ r)) =
      branchPadicReduction g p d j r := by
  unfold branchPadicRepresentative
  exact ZMod.natCast_zmod_val _

/-- The standard representative remains on the original seed branch modulo p. -/
theorem branchPadicRepresentative_seedCongr
    {g p d j r : Nat} [Fact p.Prime]
    (hrPos : 0 < r) :
    BranchSeedModP (branchSeed g p d j)
      (branchPadicRepresentative g p d j r) p := by
  unfold BranchSeedModP
  have hdiv : p ∣ p ^ r := by
    cases r with
    | zero => exact False.elim ((Nat.not_lt_zero 0) hrPos)
    | succ k =>
        rw [pow_succ]
        exact dvd_mul_left p (p ^ k)
  have hcast := congrArg
    (ZMod.castHom hdiv (ZMod p))
    (branchPadicRepresentative_cast
      (g := g) (p := p) (d := d) (j := j) (r := r))
  have hrepReduction :
      (branchPadicRepresentative g p d j r : ZMod p) =
        (ZMod.cast (branchPadicReduction g p d j r) : ZMod p) := by
    simpa only [ZMod.castHom_apply, ZMod.cast_natCast hdiv] using hcast
  exact hrepReduction.trans
    (branchPadicReduction_modP
      (g := g) (p := p) (d := d) (j := j) hrPos)

/-- The standard representative satisfies the root equation at level r. -/
theorem branchPadicRepresentative_rootAtLevel
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j) :
    RootAtLevel (branchPadicRepresentative g p d j r) p d r := by
  unfold RootAtLevel
  rw [branchPadicRepresentative_cast]
  exact branchPadicReduction_pow_eq_one hcopG hprimitive hparams

/-- The p-adic reduction, represented naturally, is itself a finite
Teichmuller lift on the concrete branch. -/
theorem branchPadicRepresentative_teichmullerLift
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    TeichmullerLiftAtLevel g p d j
      (branchPadicRepresentative g p d j r) r := by
  exact ⟨
    branchPadicRepresentative_seedCongr hrPos,
    branchPadicRepresentative_rootAtLevel hcopG hprimitive hparams⟩

/-- Every finite Teichmuller lift already constructed by Hensel is exactly the
reduction of the Witt/p-adic Teichmuller root. -/
theorem teichmullerLift_eq_branchPadicReduction
    {g p d j omega r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (hlift : TeichmullerLiftAtLevel g p d j omega r) :
    (omega : ZMod (p ^ r)) = branchPadicReduction g p d j r := by
  have hsimple : SimpleRootModP (branchSeed g p d j) p d :=
    branchSeed_simpleRoot hcopG hprimitive hparams
  rcases existsUniqueLiftAtLevel_of_simpleRoot hsimple hrPos with
    ⟨omegaCanonical, hcanonical, hunique⟩
  have homega :
      (omega : ZMod (p ^ r)) = (omegaCanonical : ZMod (p ^ r)) :=
    hunique omega hlift
  have hpadicLift :
      LiftAtLevel (branchSeed g p d j)
        (branchPadicRepresentative g p d j r) p d r :=
    branchPadicRepresentative_teichmullerLift
      hcopG hprimitive hparams hrPos
  have hpadic :
      (branchPadicRepresentative g p d j r : ZMod (p ^ r)) =
        (omegaCanonical : ZMod (p ^ r)) :=
    hunique (branchPadicRepresentative g p d j r) hpadicLift
  calc
    (omega : ZMod (p ^ r)) =
        (omegaCanonical : ZMod (p ^ r)) := homega
    _ = (branchPadicRepresentative g p d j r : ZMod (p ^ r)) := hpadic.symm
    _ = branchPadicReduction g p d j r :=
      branchPadicRepresentative_cast

/-- Stage-10 public package: one p-adic root whose every finite coordinate is
rooted on the correct branch and agrees with the finite Hensel construction. -/
structure PadicTeichmullerBridgeResult
    (g p d j : Nat) [Fact p.Prime] where
  root : ℤ_[p]
  root_eq : root = branchPadicRoot g p d j
  rootPow : root ^ d = 1
  reductionRoot : ∀ r : Nat,
    (PadicInt.toZModPow r root) ^ d = 1
  reductionSeed : ∀ r : Nat, 0 < r →
    (ZMod.cast (PadicInt.toZModPow r root) : ZMod p) =
      (branchSeed g p d j : ZMod p)
  finiteAgreement : ∀ (r omega : Nat), 0 < r →
    TeichmullerLiftAtLevel g p d j omega r →
      (omega : ZMod (p ^ r)) = PadicInt.toZModPow r root

/-- Concrete construction of the complete stage-10 Witt/p-adic bridge. -/
noncomputable def padicTeichmullerBridgeResult
    {g p d j : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j) :
    PadicTeichmullerBridgeResult g p d j := by
  refine
    { root := branchPadicRoot g p d j
      root_eq := rfl
      rootPow := branchPadicRoot_pow_eq_one hcopG hprimitive hparams
      reductionRoot := ?_
      reductionSeed := ?_
      finiteAgreement := ?_ }
  · intro r
    exact branchPadicReduction_pow_eq_one hcopG hprimitive hparams
  · intro r hrPos
    exact branchPadicReduction_modP hrPos
  · intro r omega hrPos hlift
    exact teichmullerLift_eq_branchPadicReduction
      hcopG hprimitive hparams hrPos hlift

/-- Existence spelling of the stage-10 result. -/
theorem exists_padicTeichmullerBridgeResult
    {g p d j : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j) :
    Nonempty (PadicTeichmullerBridgeResult g p d j) :=
  ⟨padicTeichmullerBridgeResult hcopG hprimitive hparams⟩

end ApparitionDepth3
