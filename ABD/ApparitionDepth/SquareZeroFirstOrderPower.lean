/-
  ABD.ApparitionDepth.SquareZeroFirstOrderPower

  Step 21V of the Apparition-Depth Decomposition project.

  This file proves the remaining square-zero first-order power rule used by the
  finite Hensel binomial bridge.

  The key algebraic fact is independent of Hensel theory:

      y*y = 0 -> (x+y)^(n+1) = x^(n+1) + y * ((n+1) * x^n).

  After proving this in a commutative semiring, we specialize it to the existing
  `ZModSquareZeroFirstOrderPowerRule` API from Step 21U.
-/

import ABD.ApparitionDepth.BinomialFirstOrderExpansionActual

namespace ApparitionDepth

universe u

/-! ## Generic square-zero first-order power rule -/

/-- Square-zero first-order power expansion in any commutative semiring.

If `y*y = 0`, then all powers of `y` of degree at least two vanish in the
expansion of `(x+y)^(n+1)`, leaving exactly the first-order term. -/
theorem squareZero_firstOrderPower_succ
    {R : Type u} [CommSemiring R]
    {x y : R} (hy : y * y = 0) :
    ∀ n : Nat,
      (x + y) ^ (Nat.succ n) =
        x ^ (Nat.succ n) +
          y * (((Nat.succ n : Nat) : R) * x ^ n) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (x + y) ^ (Nat.succ (Nat.succ n))
            = (x + y) ^ (Nat.succ n) * (x + y) := by
                rw [pow_succ]
        _ = (x ^ (Nat.succ n) +
              y * (((Nat.succ n : Nat) : R) * x ^ n)) * (x + y) := by
                rw [ih]
        _ = x ^ (Nat.succ (Nat.succ n)) +
              y * (((Nat.succ (Nat.succ n) : Nat) : R) *
                x ^ (Nat.succ n)) := by
                have hy_pow : y ^ 2 = 0 := by
                  simpa [pow_two] using hy
                ring_nf
                simp [hy_pow]
                ring_nf

/-! ## Specialization to the finite-Hensel `ZMod` API -/

/-- Actual proof of the generic square-zero first-order power rule in
`ZMod (p^(r+1))`. -/
theorem zmodSquareZeroFirstOrderPowerRule_actual (p d r : Nat) :
    ZModSquareZeroFirstOrderPowerRule p d r := by
  intro x y hy
  cases d with
  | zero =>
      simp
  | succ n =>
      simpa using
        (squareZero_firstOrderPower_succ
          (R := ZMod (p ^ (r + 1)))
          (x := x) (y := y) hy n)

/-- All-level version of the actual square-zero first-order power rule. -/
theorem zmodSquareZeroFirstOrderPowerRuleForAllLevels_actual (p d : Nat) :
    ZModSquareZeroFirstOrderPowerRuleForAllLevels p d :=
  fun r _hr_pos => zmodSquareZeroFirstOrderPowerRule_actual p d r

/-- A square-zero correction certificate now gives the finite-Hensel first-order
expansion rule without any remaining square-zero power-rule hypothesis. -/
theorem finiteHenselFirstOrderExpansionRule_of_squareZeroCorrection
    {p d r : Nat}
    (hsq : FiniteHenselSquareZeroCorrection p r) :
    FiniteHenselFirstOrderExpansionRuleAtLevel p d r :=
  finiteHenselFirstOrderExpansionRule_of_squareZeroPowerRule hsq
    (zmodSquareZeroFirstOrderPowerRule_actual p d r)

/-- All-level finite-Hensel first-order expansion from all-level square-zero
correction. -/
theorem finiteHenselFirstOrderExpansionRuleForAllLevels_of_squareZeroCorrection
    {p d : Nat}
    (hsq : FiniteHenselSquareZeroCorrectionForAllLevels p) :
    FiniteHenselFirstOrderExpansionRuleForAllLevels p d :=
  finiteHenselFirstOrderExpansionRuleForAllLevels_of_squareZeroPowerRule hsq
    (zmodSquareZeroFirstOrderPowerRuleForAllLevels_actual p d)

/-- A square-zero correction certificate now gives higher-term vanishing directly. -/
theorem finiteHenselHigherTermsVanish_of_squareZeroCorrection
    {omega omegaNext t p d r : Nat}
    (hsq : FiniteHenselSquareZeroCorrection p r) :
    FiniteHenselHigherTermsVanish omega omegaNext t p d r :=
  finiteHenselHigherTermsVanish_of_squareZeroPowerRule hsq
    (zmodSquareZeroFirstOrderPowerRule_actual p d r)

/-- A square-zero correction certificate now gives the binomial truncation directly. -/
theorem finiteHenselBinomialTruncation_of_squareZeroCorrection
    {omega omegaNext t p d r : Nat}
    (hsq : FiniteHenselSquareZeroCorrection p r)
    (hstep : FiniteHenselStepRelation omega omegaNext t p r) :
    FiniteHenselBinomialTruncation omega omegaNext t p d r :=
  finiteHenselBinomialTruncation_of_squareZeroPowerRule hsq
    (zmodSquareZeroFirstOrderPowerRule_actual p d r) hstep

end ApparitionDepth
