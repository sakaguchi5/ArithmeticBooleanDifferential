/-
  ABD.ApparitionDepth.HigherTermsVanish

  Step 21E-2 of the Apparition-Depth Decomposition project.

  This file names the vanishing of the higher binomial terms in a one-step finite
  Hensel correction.  It is intentionally separated from the transport layer so
  that the later concrete proof can focus only on the divisibility of those
  higher terms.
-/

import ABD.ApparitionDepth.BinomialTruncation

namespace ApparitionDepth

/-! ## Higher-term vanishing certificate -/

/-- Higher terms vanish for a concrete one-step correction.

This is the precise local algebraic certificate that turns a correction step
relation into the first-order binomial truncation. -/
def FiniteHenselHigherTermsVanish
    (omega omegaNext t p d r : Nat) : Prop :=
  FiniteHenselStepRelation omega omegaNext t p r →
    FiniteHenselBinomialTruncation omega omegaNext t p d r

/-- Constructor for the higher-term vanishing certificate. -/
theorem finiteHenselHigherTermsVanish_intro
    {omega omegaNext t p d r : Nat}
    (h : FiniteHenselStepRelation omega omegaNext t p r →
      FiniteHenselBinomialTruncation omega omegaNext t p d r) :
    FiniteHenselHigherTermsVanish omega omegaNext t p d r :=
  h

/-- Apply the higher-term vanishing certificate. -/
theorem finiteHenselHigherTermsVanish_apply
    {omega omegaNext t p d r : Nat}
    (hvanish : FiniteHenselHigherTermsVanish omega omegaNext t p d r)
    (hstep : FiniteHenselStepRelation omega omegaNext t p r) :
    FiniteHenselBinomialTruncation omega omegaNext t p d r :=
  hvanish hstep

/-- A bundle containing a candidate step together with the proof that its higher
terms vanish. -/
def FiniteHenselTruncatedStep
    (omega omegaNext t p d r : Nat) : Prop :=
  FiniteHenselStepRelation omega omegaNext t p r ∧
    FiniteHenselHigherTermsVanish omega omegaNext t p d r

/-- Constructor for a truncated step. -/
theorem finiteHenselTruncatedStep_intro
    {omega omegaNext t p d r : Nat}
    (hstep : FiniteHenselStepRelation omega omegaNext t p r)
    (hvanish : FiniteHenselHigherTermsVanish omega omegaNext t p d r) :
    FiniteHenselTruncatedStep omega omegaNext t p d r :=
  ⟨hstep, hvanish⟩

/-- Projection: the underlying step relation. -/
theorem finiteHenselTruncatedStep_step
    {omega omegaNext t p d r : Nat}
    (h : FiniteHenselTruncatedStep omega omegaNext t p d r) :
    FiniteHenselStepRelation omega omegaNext t p r :=
  h.1

/-- Projection: the higher-term vanishing certificate. -/
theorem finiteHenselTruncatedStep_vanish
    {omega omegaNext t p d r : Nat}
    (h : FiniteHenselTruncatedStep omega omegaNext t p d r) :
    FiniteHenselHigherTermsVanish omega omegaNext t p d r :=
  h.2

/-- A truncated step gives the first-order binomial truncation. -/
theorem finiteHenselBinomialTruncation_of_truncatedStep
    {omega omegaNext t p d r : Nat}
    (h : FiniteHenselTruncatedStep omega omegaNext t p d r) :
    FiniteHenselBinomialTruncation omega omegaNext t p d r :=
  finiteHenselHigherTermsVanish_apply
    (finiteHenselTruncatedStep_vanish h)
    (finiteHenselTruncatedStep_step h)

end ApparitionDepth
