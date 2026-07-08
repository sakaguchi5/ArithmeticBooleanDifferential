/-
  ABD.ApparitionDepth.HigherTermsVanishProof

  Step 21J of the Apparition-Depth Decomposition project.

  This file connects a direct binomial-expansion rule to the higher-terms-vanish
  certificate consumed by Step 21E.
-/

import ABD.ApparitionDepth.BinomialExpansionCore

namespace ApparitionDepth

/-! ## Higher terms vanish from the binomial expansion core -/

/-- A direct higher-term vanishing proof rule at level `r`.

Mathematically, this is where one proves that all terms with exponent at least
`2` in `(omega + t*p^r)^d` are divisible by `p^(r+1)`. -/
def FiniteHenselHigherTermsVanishRule (p d r : Nat) : Prop :=
  ∀ omega omegaNext t : Nat,
    FiniteHenselStepRelation omega omegaNext t p r →
      FiniteHenselHigherTermsVanish omega omegaNext t p d r

/-- A binomial expansion core rule gives the higher-terms-vanish rule. -/
theorem finiteHenselHigherTermsVanishRule_of_expansionCoreRule
    {p d r : Nat}
    (hrule : FiniteHenselBinomialExpansionCoreRule p d r) :
    FiniteHenselHigherTermsVanishRule p d r := by
  intro omega omegaNext t hstep _hstepAgain
  exact finiteHenselBinomialTruncation_of_expansionCore
    (finiteHenselBinomialExpansionCoreRule_apply hrule hstep)

/-- Apply a higher-terms-vanish rule. -/
theorem finiteHenselHigherTermsVanish_of_rule
    {omega omegaNext t p d r : Nat}
    (hrule : FiniteHenselHigherTermsVanishRule p d r)
    (hstep : FiniteHenselStepRelation omega omegaNext t p r) :
    FiniteHenselHigherTermsVanish omega omegaNext t p d r :=
  hrule omega omegaNext t hstep

/-- A step relation plus a higher-terms-vanish rule gives a truncated step. -/
theorem finiteHenselTruncatedStep_of_higherTermsRule
    {omega omegaNext t p d r : Nat}
    (hrule : FiniteHenselHigherTermsVanishRule p d r)
    (hstep : FiniteHenselStepRelation omega omegaNext t p r) :
    FiniteHenselTruncatedStep omega omegaNext t p d r :=
  finiteHenselTruncatedStep_intro hstep
    (finiteHenselHigherTermsVanish_of_rule hrule hstep)

/-- All-level higher-terms-vanish rule. -/
def FiniteHenselHigherTermsVanishForAllLevels (p d : Nat) : Prop :=
  ∀ r : Nat, 0 < r → FiniteHenselHigherTermsVanishRule p d r

/-- Extract one level from the all-level rule. -/
theorem finiteHenselHigherTermsVanishForAllLevels_at
    {p d r : Nat}
    (h : FiniteHenselHigherTermsVanishForAllLevels p d)
    (hr_pos : 0 < r) :
    FiniteHenselHigherTermsVanishRule p d r :=
  h r hr_pos

end ApparitionDepth
