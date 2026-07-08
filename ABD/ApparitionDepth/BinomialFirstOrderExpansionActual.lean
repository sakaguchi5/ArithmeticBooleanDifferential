/-
  ABD.ApparitionDepth.BinomialFirstOrderExpansionActual

  Step 21U of the Apparition-Depth Decomposition project.

  This file builds the concrete bridge for the remaining binomial/Hensel step.
  The hard expansion is reduced to the standard square-zero first-order power
  rule:

      y*y = 0 -> (x+y)^d = x^d + y * d*x^(d-1).

  In the Hensel application, `y = t*p^r` in `ZMod (p^(r+1))`.  Once the
  correction term is known to be square-zero at that precision, the square-zero
  power rule gives exactly `FiniteHenselFirstOrderExpansionRule`, and therefore
  the existing binomial truncation / higher-terms-vanish APIs.
-/

import ABD.ApparitionDepth.PrimeNeZeroBridge
import ABD.ApparitionDepth.HigherTermPowerDivisibilityActual

namespace ApparitionDepth

/-! ## Square-zero correction term -/

/-- The correction modulus factor `p^r` is square-zero at precision `p^(r+1)`.

This is the local ring-theoretic form of the already-proved divisibility fact
`p^(r+1) | p^(2*r)` for `0 < r`. -/
def FiniteHenselSquareZeroCorrection (p r : Nat) : Prop :=
  (p ^ r : ZMod (p ^ (r + 1))) *
    (p ^ r : ZMod (p ^ (r + 1))) = 0

/-- Constructor for the square-zero correction certificate. -/
theorem finiteHenselSquareZeroCorrection_intro {p r : Nat}
    (h : (p ^ r : ZMod (p ^ (r + 1))) *
      (p ^ r : ZMod (p ^ (r + 1))) = 0) :
    FiniteHenselSquareZeroCorrection p r :=
  h

/-- Projection from the square-zero correction certificate. -/
theorem finiteHenselSquareZeroCorrection_eq {p r : Nat}
    (h : FiniteHenselSquareZeroCorrection p r) :
    (p ^ r : ZMod (p ^ (r + 1))) *
      (p ^ r : ZMod (p ^ (r + 1))) = 0 :=
  h

/-- The actual correction digit `t*p^r` is square-zero whenever `p^r` is
square-zero at precision `p^(r+1)`. -/
theorem finiteHenselCorrectionDigit_squareZero
    {t p r : Nat}
    (hsq : FiniteHenselSquareZeroCorrection p r) :
    ((t : ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1)))) *
      ((t : ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1)))) = 0 := by
  have hbase := finiteHenselSquareZeroCorrection_eq hsq
  calc
    ((t : ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1)))) *
      ((t : ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1))))
        = ((t : ZMod (p ^ (r + 1))) * (t : ZMod (p ^ (r + 1)))) *
            ((p ^ r : ZMod (p ^ (r + 1))) *
              (p ^ r : ZMod (p ^ (r + 1)))) := by
            ring
    _ = ((t : ZMod (p ^ (r + 1))) * (t : ZMod (p ^ (r + 1)))) * 0 := by
            rw [hbase]
    _ = 0 := by
            rw [mul_zero]

/-! ## Generic square-zero first-order power rule -/

/-- Generic first-order power rule in the finite ring `ZMod (p^(r+1))`.

This is the remaining direct binomial-theorem target.  It is intentionally stated
separately from the Hensel notation: prove this once, and the Hensel first-order
expansion follows by substitution. -/
def ZModSquareZeroFirstOrderPowerRule (p d r : Nat) : Prop :=
  ∀ x y : ZMod (p ^ (r + 1)),
    y * y = 0 →
      (x + y) ^ d =
        x ^ d + y * ((d : ZMod (p ^ (r + 1))) * x ^ (d - 1))

/-- Constructor for the generic square-zero power rule. -/
theorem zmodSquareZeroFirstOrderPowerRule_intro {p d r : Nat}
    (h : ∀ x y : ZMod (p ^ (r + 1)),
      y * y = 0 →
        (x + y) ^ d =
          x ^ d + y * ((d : ZMod (p ^ (r + 1))) * x ^ (d - 1))) :
    ZModSquareZeroFirstOrderPowerRule p d r :=
  h

/-- Apply the generic square-zero power rule. -/
theorem zmodSquareZeroFirstOrderPowerRule_apply
    {p d r : Nat}
    (hrule : ZModSquareZeroFirstOrderPowerRule p d r)
    {x y : ZMod (p ^ (r + 1))}
    (hy : y * y = 0) :
    (x + y) ^ d =
      x ^ d + y * ((d : ZMod (p ^ (r + 1))) * x ^ (d - 1)) :=
  hrule x y hy

/-! ## From square-zero power rule to the Hensel first-order expansion -/

/-- At one level, the square-zero correction and the generic square-zero power
rule imply the Hensel first-order expansion rule. -/
theorem finiteHenselFirstOrderExpansionRule_of_squareZeroPowerRule
    {p d r : Nat}
    (hsq : FiniteHenselSquareZeroCorrection p r)
    (hrule : ZModSquareZeroFirstOrderPowerRule p d r) :
    FiniteHenselFirstOrderExpansionRuleAtLevel p d r := by
  intro omega omegaNext t
  unfold FiniteHenselFirstOrderExpansionRule
  intro hstep
  unfold FiniteHenselFirstOrderExpansion
  let y : ZMod (p ^ (r + 1)) :=
    (t : ZMod (p ^ (r + 1))) *
      (p ^ r : ZMod (p ^ (r + 1)))
  have hy : y * y = 0 := by
    dsimp [y]
    exact finiteHenselCorrectionDigit_squareZero hsq
  have hformula :
      (omegaNext : ZMod (p ^ (r + 1))) =
        (omega : ZMod (p ^ (r + 1))) + y := by
    dsimp [y]
    exact finiteHenselStepRelation_formula hstep
  calc
    (omegaNext : ZMod (p ^ (r + 1))) ^ d
        = ((omega : ZMod (p ^ (r + 1))) + y) ^ d := by
            rw [hformula]
    _ = (omega : ZMod (p ^ (r + 1))) ^ d +
          y * ((d : ZMod (p ^ (r + 1))) *
            (omega : ZMod (p ^ (r + 1))) ^ (d - 1)) :=
            zmodSquareZeroFirstOrderPowerRule_apply hrule hy
    _ = (omega : ZMod (p ^ (r + 1))) ^ d +
          ((t : ZMod (p ^ (r + 1))) *
            (p ^ r : ZMod (p ^ (r + 1)))) *
              finiteHenselDerivativeAtLevel omega p d r := by
            dsimp [y, finiteHenselDerivativeAtLevel]

/-- All-level version of the previous bridge. -/
def FiniteHenselSquareZeroCorrectionForAllLevels (p : Nat) : Prop :=
  ∀ r : Nat, 0 < r → FiniteHenselSquareZeroCorrection p r

/-- All-level generic square-zero first-order power rule. -/
def ZModSquareZeroFirstOrderPowerRuleForAllLevels (p d : Nat) : Prop :=
  ∀ r : Nat, 0 < r → ZModSquareZeroFirstOrderPowerRule p d r

/-- All-level Hensel first-order expansion from square-zero correction and the
square-zero power rule. -/
theorem finiteHenselFirstOrderExpansionRuleForAllLevels_of_squareZeroPowerRule
    {p d : Nat}
    (hsq : FiniteHenselSquareZeroCorrectionForAllLevels p)
    (hrule : ZModSquareZeroFirstOrderPowerRuleForAllLevels p d) :
    FiniteHenselFirstOrderExpansionRuleForAllLevels p d :=
  fun r hr_pos =>
    finiteHenselFirstOrderExpansionRule_of_squareZeroPowerRule
      (hsq r hr_pos) (hrule r hr_pos)

/-- The resulting higher-term vanishing certificate, in the existing API. -/
theorem finiteHenselHigherTermsVanish_of_squareZeroPowerRule
    {omega omegaNext t p d r : Nat}
    (hsq : FiniteHenselSquareZeroCorrection p r)
    (hrule : ZModSquareZeroFirstOrderPowerRule p d r) :
    FiniteHenselHigherTermsVanish omega omegaNext t p d r :=
  finiteHenselHigherTermsVanish_of_firstOrderRule
    ((finiteHenselFirstOrderExpansionRule_of_squareZeroPowerRule hsq hrule)
      omega omegaNext t)

/-- The resulting binomial truncation certificate, in the existing API. -/
theorem finiteHenselBinomialTruncation_of_squareZeroPowerRule
    {omega omegaNext t p d r : Nat}
    (hsq : FiniteHenselSquareZeroCorrection p r)
    (hrule : ZModSquareZeroFirstOrderPowerRule p d r)
    (hstep : FiniteHenselStepRelation omega omegaNext t p r) :
    FiniteHenselBinomialTruncation omega omegaNext t p d r :=
  finiteHenselBinomialTruncation_of_firstOrderRule
    ((finiteHenselFirstOrderExpansionRule_of_squareZeroPowerRule hsq hrule)
      omega omegaNext t)
    hstep

end ApparitionDepth
