/-
  ABD.ApparitionDepth.BinomialExpansionCore

  Step 21I of the Apparition-Depth Decomposition project.

  This file names the concrete binomial-expansion core used by the one-step
  Hensel lift.  The API is intentionally small: a future proof of the binomial
  theorem modulo `p^(r+1)` can target this certificate directly.
-/

import ABD.ApparitionDepth.BranchDerivativeUnit

namespace ApparitionDepth

/-! ## Binomial expansion core -/

/-- The core first-order binomial expansion certificate for one correction step.

This is extensionally the same data as `FiniteHenselBinomialTruncation`; it is
introduced as a more explicit target for the later actual binomial proof. -/
def FiniteHenselBinomialExpansionCore
    (omega omegaNext t p d r : Nat) : Prop :=
  FiniteHenselBinomialTruncation omega omegaNext t p d r

/-- Constructor for the binomial expansion core from the existing truncation
certificate. -/
theorem finiteHenselBinomialExpansionCore_intro
    {omega omegaNext t p d r : Nat}
    (h : FiniteHenselBinomialTruncation omega omegaNext t p d r) :
    FiniteHenselBinomialExpansionCore omega omegaNext t p d r :=
  h

/-- Projection back to the existing truncation certificate. -/
theorem finiteHenselBinomialTruncation_of_expansionCore
    {omega omegaNext t p d r : Nat}
    (h : FiniteHenselBinomialExpansionCore omega omegaNext t p d r) :
    FiniteHenselBinomialTruncation omega omegaNext t p d r :=
  h

/-- A binomial expansion core gives the step relation. -/
theorem finiteHenselBinomialExpansionCore_step
    {omega omegaNext t p d r : Nat}
    (h : FiniteHenselBinomialExpansionCore omega omegaNext t p d r) :
    FiniteHenselStepRelation omega omegaNext t p r :=
  finiteHenselBinomialTruncation_step
    (finiteHenselBinomialTruncation_of_expansionCore h)

/-- A binomial expansion core gives the first-order truncation equality. -/
theorem finiteHenselBinomialExpansionCore_eq
    {omega omegaNext t p d r : Nat}
    (h : FiniteHenselBinomialExpansionCore omega omegaNext t p d r) :
    (omegaNext : ZMod (p ^ (r + 1))) ^ d =
      (omega : ZMod (p ^ (r + 1))) ^ d +
        ((t : ZMod (p ^ (r + 1))) *
          (p ^ r : ZMod (p ^ (r + 1)))) *
            finiteHenselDerivativeAtLevel omega p d r :=
  finiteHenselBinomialTruncation_eq
    (finiteHenselBinomialTruncation_of_expansionCore h)

/-- The expected theorem-shape for a future direct binomial proof. -/
def FiniteHenselBinomialExpansionCoreRule (p d r : Nat) : Prop :=
  ∀ omega omegaNext t : Nat,
    FiniteHenselStepRelation omega omegaNext t p r →
      FiniteHenselBinomialExpansionCore omega omegaNext t p d r

/-- Apply a binomial expansion core rule. -/
theorem finiteHenselBinomialExpansionCoreRule_apply
    {omega omegaNext t p d r : Nat}
    (hrule : FiniteHenselBinomialExpansionCoreRule p d r)
    (hstep : FiniteHenselStepRelation omega omegaNext t p r) :
    FiniteHenselBinomialExpansionCore omega omegaNext t p d r :=
  hrule omega omegaNext t hstep

end ApparitionDepth
