/-
  ABD.ApparitionDepth.SquareZeroCorrectionActual

  Step 21W of the Apparition-Depth Decomposition project.

  This file closes the remaining square-zero bridge in the binomial/Hensel route.
  The previous file proved the square-zero first-order power rule.  What remained
  was to show that the Hensel correction factor `p^r` is actually square-zero in
  `ZMod (p^(r+1))` whenever `0 < r`.

  Concretely:

      p^(r+1) | p^r * p^r
      ----------------------
      (p^r : ZMod (p^(r+1))) * (p^r : ZMod (p^(r+1))) = 0

  This completes the binomial first-order expansion route for every positive
  level.
-/

import ABD.ApparitionDepth.SquareZeroFirstOrderPower

namespace ApparitionDepth

/-! ## Casting a divisible natural number to zero in `ZMod` -/

/-- If `n` divides a natural number `a`, then the image of `a` in `ZMod n` is zero.

This small bridge is the exact conversion needed to pass from the natural-number
power divisibility statement to the square-zero statement in the finite quotient
ring. -/
theorem zmod_natCast_eq_zero_of_dvd {n a : Nat}
    (h : n ∣ a) :
    ((a : Nat) : ZMod n) = 0 := by
  rw [show (0 : ZMod n) = ((0 : Nat) : ZMod n) by norm_num]
  rw [ZMod.natCast_eq_natCast_iff]
  have hmod : 0 ≡ a [MOD n] := by
    exact (Nat.modEq_iff_dvd' (n := n) (a := 0) (b := a) (Nat.zero_le a)).mpr h
  simpa [Nat.ModEq.comm] using hmod

/-! ## Actual square-zero correction -/

/-- A divisibility statement for `p^r * p^r` gives the square-zero correction
certificate. -/
theorem finiteHenselSquareZeroCorrection_of_dvd
    {p r : Nat}
    (h : p ^ (r + 1) ∣ p ^ r * p ^ r) :
    FiniteHenselSquareZeroCorrection p r := by
  refine finiteHenselSquareZeroCorrection_intro ?_
  simpa [Nat.cast_mul] using
    (zmod_natCast_eq_zero_of_dvd
      (n := p ^ (r + 1))
      (a := p ^ r * p ^ r) h)

/-- Actual square-zero correction at every positive level.

This uses the already-proved pure arithmetic target
`p^(r+1) | p^(r*2)`, together with `p^(r*2) = p^r*p^r`. -/
theorem finiteHenselSquareZeroCorrection_actual (p r : Nat)
    (hr_pos : 0 < r) :
    FiniteHenselSquareZeroCorrection p r := by
  apply finiteHenselSquareZeroCorrection_of_dvd
  have hpow : p ^ (r + 1) ∣ p ^ (r * 2) :=
    pow_succ_dvd_pow_mul_of_two_le_of_pos p r 2 (by decide) hr_pos
  simpa [Nat.mul_two, pow_add] using hpow

/-- All-level actual square-zero correction. -/
theorem finiteHenselSquareZeroCorrectionForAllLevels_actual (p : Nat) :
    FiniteHenselSquareZeroCorrectionForAllLevels p :=
  fun r hr_pos => finiteHenselSquareZeroCorrection_actual p r hr_pos

/-! ## Completed binomial first-order route -/

/-- The finite-Hensel first-order expansion rule is now available at every positive
level, with no remaining square-zero hypothesis. -/
theorem finiteHenselFirstOrderExpansionRuleAtLevel_actual
    (p d r : Nat) (hr_pos : 0 < r) :
    FiniteHenselFirstOrderExpansionRuleAtLevel p d r :=
  finiteHenselFirstOrderExpansionRule_of_squareZeroCorrection
    (finiteHenselSquareZeroCorrection_actual p r hr_pos)

/-- All-level finite-Hensel first-order expansion rule. -/
theorem finiteHenselFirstOrderExpansionRuleForAllLevels_actual
    (p d : Nat) :
    FiniteHenselFirstOrderExpansionRuleForAllLevels p d :=
  finiteHenselFirstOrderExpansionRuleForAllLevels_of_squareZeroCorrection
    (finiteHenselSquareZeroCorrectionForAllLevels_actual p)

/-- Higher-term vanishing is now available directly at every positive level. -/
theorem finiteHenselHigherTermsVanish_actual
    {omega omegaNext t p d r : Nat}
    (hr_pos : 0 < r) :
    FiniteHenselHigherTermsVanish omega omegaNext t p d r :=
  finiteHenselHigherTermsVanish_of_squareZeroCorrection
    (finiteHenselSquareZeroCorrection_actual p r hr_pos)

/-- Binomial truncation is now available directly at every positive level from the
one-step relation. -/
theorem finiteHenselBinomialTruncation_actual
    {omega omegaNext t p d r : Nat}
    (hr_pos : 0 < r)
    (hstep : FiniteHenselStepRelation omega omegaNext t p r) :
    FiniteHenselBinomialTruncation omega omegaNext t p d r :=
  finiteHenselBinomialTruncation_of_squareZeroCorrection
    (finiteHenselSquareZeroCorrection_actual p r hr_pos) hstep

/-- Compatibility with the older first-order rule API from Step 21Q. -/
theorem finiteHenselFirstOrderExpansionRuleForAllLevels_completed
    (p d : Nat) :
    FiniteHenselFirstOrderExpansionRuleForAllLevels p d :=
  finiteHenselFirstOrderExpansionRuleForAllLevels_actual p d

end ApparitionDepth
