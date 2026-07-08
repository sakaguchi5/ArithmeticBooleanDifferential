/-
  ABD.ApparitionDepth.BinomialHigherTermsActualProof

  Step 21Q of the Apparition-Depth Decomposition project.

  This file makes the remaining binomial/higher-term proof obligation as small as
  possible.  The target is reduced to an explicit first-order expansion rule; from
  that rule we obtain `FiniteHenselHigherTermsVanish` and hence the truncation
  certificate consumed by the one-step Hensel pipeline.
-/

import ABD.ApparitionDepth.QuotientCorrectionAssembly

namespace ApparitionDepth

/-! ## Explicit binomial expansion target -/

/-- The raw first-order binomial equality at precision `p^(r+1)`.

This is the exact equality that the concrete binomial theorem plus higher-term
vanishing must prove. -/
def FiniteHenselFirstOrderExpansion
    (omega omegaNext t p d r : Nat) : Prop :=
  (omegaNext : ZMod (p ^ (r + 1))) ^ d =
    (omega : ZMod (p ^ (r + 1))) ^ d +
      ((t : ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1)))) *
          finiteHenselDerivativeAtLevel omega p d r

/-- A rule proving the first-order expansion from the one-step relation. -/
def FiniteHenselFirstOrderExpansionRule
    (omega omegaNext t p d r : Nat) : Prop :=
  FiniteHenselStepRelation omega omegaNext t p r →
    FiniteHenselFirstOrderExpansion omega omegaNext t p d r

/-- Constructor for the raw first-order expansion. -/
theorem finiteHenselFirstOrderExpansion_intro
    {omega omegaNext t p d r : Nat}
    (h : (omegaNext : ZMod (p ^ (r + 1))) ^ d =
      (omega : ZMod (p ^ (r + 1))) ^ d +
        ((t : ZMod (p ^ (r + 1))) *
          (p ^ r : ZMod (p ^ (r + 1)))) *
            finiteHenselDerivativeAtLevel omega p d r) :
    FiniteHenselFirstOrderExpansion omega omegaNext t p d r :=
  h

/-- Projection from the raw first-order expansion. -/
theorem finiteHenselFirstOrderExpansion_eq
    {omega omegaNext t p d r : Nat}
    (h : FiniteHenselFirstOrderExpansion omega omegaNext t p d r) :
    (omegaNext : ZMod (p ^ (r + 1))) ^ d =
      (omega : ZMod (p ^ (r + 1))) ^ d +
        ((t : ZMod (p ^ (r + 1))) *
          (p ^ r : ZMod (p ^ (r + 1)))) *
            finiteHenselDerivativeAtLevel omega p d r :=
  h

/-- A first-order expansion rule gives the existing binomial truncation
certificate. -/
theorem finiteHenselBinomialTruncation_of_firstOrderRule
    {omega omegaNext t p d r : Nat}
    (hrule : FiniteHenselFirstOrderExpansionRule omega omegaNext t p d r)
    (hstep : FiniteHenselStepRelation omega omegaNext t p r) :
    FiniteHenselBinomialTruncation omega omegaNext t p d r :=
  finiteHenselBinomialTruncation_intro hstep
    (finiteHenselFirstOrderExpansion_eq (hrule hstep))

/-- A first-order expansion rule gives higher-term vanishing in the existing API. -/
theorem finiteHenselHigherTermsVanish_of_firstOrderRule
    {omega omegaNext t p d r : Nat}
    (hrule : FiniteHenselFirstOrderExpansionRule omega omegaNext t p d r) :
    FiniteHenselHigherTermsVanish omega omegaNext t p d r := by
  intro hstep
  exact finiteHenselBinomialTruncation_of_firstOrderRule hrule hstep

/-- Level-wise rule: every concrete correction step at a level satisfies the
first-order expansion. -/
def FiniteHenselFirstOrderExpansionRuleAtLevel (p d r : Nat) : Prop :=
  ∀ omega omegaNext t : Nat,
    FiniteHenselFirstOrderExpansionRule omega omegaNext t p d r

/-- All-level first-order expansion rule. -/
def FiniteHenselFirstOrderExpansionRuleForAllLevels (p d : Nat) : Prop :=
  ∀ r : Nat, 0 < r → FiniteHenselFirstOrderExpansionRuleAtLevel p d r

/-- Extract a concrete higher-term vanishing certificate from the all-level rule. -/
theorem finiteHenselHigherTermsVanish_of_firstOrderForAllLevels
    {omega omegaNext t p d r : Nat}
    (hrules : FiniteHenselFirstOrderExpansionRuleForAllLevels p d)
    (hr_pos : 0 < r) :
    FiniteHenselHigherTermsVanish omega omegaNext t p d r :=
  finiteHenselHigherTermsVanish_of_firstOrderRule
    ((hrules r hr_pos) omega omegaNext t)

/-! ## Divisibility target for the concrete proof -/

/-- The pure divisibility target behind the higher-term vanishing proof.

For `k >= 2`, the term containing `(p^r)^k` should vanish modulo `p^(r+1)`.
This predicate isolates that arithmetic target without committing to a particular
binomial-sum API yet. -/
def HigherTermPowerDivisibilityTarget (p r k : Nat) : Prop :=
  2 ≤ k → 0 < r → p ^ (r + 1) ∣ p ^ (r * k)

/-- A level-wise divisibility target for all higher powers. -/
def HigherTermPowerDivisibilityForAllHigher (p r : Nat) : Prop :=
  ∀ k : Nat, HigherTermPowerDivisibilityTarget p r k

end ApparitionDepth
