/-
  ABD.ApparitionDepth3.WittCarryBridge

  Stage 11, second half:
    * identify the ordinary p-adic next digit with the finite Hensel correction;
    * state the zero-carry criterion for the p-adic digit sequence;
    * record explicitly that Witt coefficients and ordinary p-adic digits are
      different coordinate systems.
-/

import ABD.ApparitionDepth3.PadicDigit

namespace ApparitionDepth3

/-- The ordinary next digit of the branch p-adic root is exactly the canonical
Hensel correction digit computed from the lower finite representative. -/
theorem branchPadicDigit_eq_henselCorrection
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    branchPadicDigit g p d j r =
      HenselCorrectionDigit
        (branchPadicRepresentative g p d j r) p d r
        (derivativeUnit_of_seedCongr
          (branchSeed_simpleRoot hcopG hprimitive hparams)
          (branchPadicRepresentative_teichmullerLift
            hcopG hprimitive hparams hrPos).1) := by
  let seed := branchSeed g p d j
  let lower := branchPadicRepresentative g p d j r
  let digit := branchPadicDigitNat g p d j r
  have hsimple : SimpleRootModP seed p d := by
    simpa only [seed] using branchSeed_simpleRoot hcopG hprimitive hparams
  have hlift : LiftAtLevel seed lower p d r := by
    simpa only [seed, lower, TeichmullerLiftAtLevel] using
      (branchPadicRepresentative_teichmullerLift
        hcopG hprimitive hparams hrPos)
  have hupperRoot :
      RootAtLevel (branchPadicRepresentative g p d j (r + 1)) p d (r + 1) :=
    branchPadicRepresentative_rootAtLevel hcopG hprimitive hparams
  have hdigitRoot :
      RootAtLevel (correctedRepresentative lower digit p r) p d (r + 1) := by
    rw [← show branchPadicRepresentative g p d j (r + 1) =
      correctedRepresentative lower digit p r by
        simpa only [lower, digit] using
          (branchPadicRepresentative_succ_eq_corrected
            (g := g) (p := p) (d := d) (j := j) (r := r))]
    exact hupperRoot
  have hcanonical :=
    (rootAtNextLevel_iff_digit_eq_canonical
      (seed := seed) (omega := lower) (t := digit)
      hsimple hrPos hlift).mp hdigitRoot
  simpa only [branchPadicDigit, seed, lower, digit, TeichmullerLiftAtLevel] using
    hcanonical

/-- Digit-form correction equation for the actual p-adic coordinate sequence. -/
theorem branchPadicDigit_correctionEquation
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    HenselErrorDigit (branchPadicRepresentative g p d j r) p d r +
        branchPadicDigit g p d j r *
          derivativeAt (branchPadicRepresentative g p d j r) p d =
      0 := by
  let hsimple := branchSeed_simpleRoot hcopG hprimitive hparams
  let hlift := branchPadicRepresentative_teichmullerLift
    hcopG hprimitive hparams hrPos
  let hunit : IsUnit
      (derivativeAt (branchPadicRepresentative g p d j r) p d) :=
    derivativeUnit_of_seedCongr hsimple hlift.1
  have hEq := canonicalCorrectionEquation_digit_form
    (omega := branchPadicRepresentative g p d j r) (r := r) hunit
  rw [← branchPadicDigit_eq_henselCorrection
    hcopG hprimitive hparams hrPos] at hEq
  exact hEq

/-- Zero ordinary p-adic digit is exactly zero Hensel error. -/
theorem branchPadicDigit_eq_zero_iff_errorDigit_eq_zero
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    branchPadicDigit g p d j r = 0 ↔
      HenselErrorDigit (branchPadicRepresentative g p d j r) p d r = 0 := by
  let hsimple := branchSeed_simpleRoot hcopG hprimitive hparams
  let hlift := branchPadicRepresentative_teichmullerLift
    hcopG hprimitive hparams hrPos
  let hunit : IsUnit
      (derivativeAt (branchPadicRepresentative g p d j r) p d) :=
    derivativeUnit_of_seedCongr hsimple hlift.1
  rw [branchPadicDigit_eq_henselCorrection
    hcopG hprimitive hparams hrPos]
  exact correctionDigit_eq_zero_iff_errorDigit_eq_zero hunit

/-- Zero ordinary p-adic digit is exactly survival of the current standard
representative to the next precision without changing the representative. -/
theorem branchPadicDigit_eq_zero_iff_rootAtNextLevel
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    branchPadicDigit g p d j r = 0 ↔
      RootAtLevel (branchPadicRepresentative g p d j r) p d (r + 1) := by
  rw [branchPadicDigit_eq_zero_iff_errorDigit_eq_zero
    hcopG hprimitive hparams hrPos]
  exact (rootAtNextLevel_iff_errorDigit_zero
    (branchSeed_simpleRoot hcopG hprimitive hparams)
    hrPos
    (branchPadicRepresentative_teichmullerLift
      hcopG hprimitive hparams hrPos)).symm

/-- The zeroth Witt coefficient is the selected branch residue. -/
theorem branchWittRoot_coeff_zero
    {g p d j : Nat} [Fact p.Prime] :
    (branchWittRoot g p d j).coeff 0 = branchResidue g p d j := by
  unfold branchWittRoot
  exact WittVector.teichmuller_coeff_zero _ _

/-- Every positive Witt coefficient of the Teichmuller vector is zero. -/
theorem branchWittRoot_coeff_pos
    {g p d j n : Nat} [Fact p.Prime]
    (hn : 0 < n) :
    (branchWittRoot g p d j).coeff n = 0 := by
  unfold branchWittRoot
  exact WittVector.teichmuller_coeff_pos _ _ n hn

/-- Public stage-11 package for one positive finite level.

The `ordinaryDigit` field belongs to the ordinary base-p expansion of the
p-adic integer.  The final field records the simultaneous fact that the
positive Witt coefficient is zero; no identification between the two
coordinate systems is asserted. -/
structure PadicWittCarryBridgeResult
    (g p d j r : Nat) [Fact p.Prime] where
  lowerRepresentative : Nat
  upperRepresentative : Nat
  ordinaryDigit : Nat
  lower_eq : lowerRepresentative = branchPadicRepresentative g p d j r
  upper_eq : upperRepresentative = branchPadicRepresentative g p d j (r + 1)
  digit_eq : ordinaryDigit = branchPadicDigitNat g p d j r
  digit_lt : ordinaryDigit < p
  decomposition :
    upperRepresentative = lowerRepresentative + ordinaryDigit * p ^ r
  correctionEquation :
    HenselErrorDigit lowerRepresentative p d r +
        (ordinaryDigit : ZMod p) * derivativeAt lowerRepresentative p d =
      0
  zeroCarry :
    ((ordinaryDigit : ZMod p) = 0 ↔
      RootAtLevel lowerRepresentative p d (r + 1))
  positiveWittCoefficientZero :
    (branchWittRoot g p d j).coeff (r + 1) = 0

/-- Concrete construction of the stage-11 digit/carry/Witt boundary package. -/
noncomputable def padicWittCarryBridgeResult
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    PadicWittCarryBridgeResult g p d j r := by
  refine
    { lowerRepresentative := branchPadicRepresentative g p d j r
      upperRepresentative := branchPadicRepresentative g p d j (r + 1)
      ordinaryDigit := branchPadicDigitNat g p d j r
      lower_eq := rfl
      upper_eq := rfl
      digit_eq := rfl
      digit_lt := branchPadicDigitNat_lt_prime
      decomposition := branchPadicRepresentative_succ_decomposition
      correctionEquation := ?_
      zeroCarry := ?_
      positiveWittCoefficientZero := branchWittRoot_coeff_pos (Nat.succ_pos r) }
  · simpa only [branchPadicDigit] using
      (branchPadicDigit_correctionEquation
        hcopG hprimitive hparams hrPos)
  · simpa only [branchPadicDigit] using
      (branchPadicDigit_eq_zero_iff_rootAtNextLevel
        hcopG hprimitive hparams hrPos)

/-- Existence spelling of the complete stage-11 bridge. -/
theorem exists_padicWittCarryBridgeResult
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    Nonempty (PadicWittCarryBridgeResult g p d j r) :=
  ⟨padicWittCarryBridgeResult hcopG hprimitive hparams hrPos⟩

end ApparitionDepth3
