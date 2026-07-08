/-
  ABD.ApparitionDepth.BinomialTruncation

  Step 21E-1 of the Apparition-Depth Decomposition project.

  This file isolates the first-order binomial truncation needed for one finite
  Hensel step.  The heavy algebraic proof of this truncation is represented by a
  named certificate; later files consume the certificate and push it into the
  existing finite-Hensel step interfaces.
-/

import ABD.ApparitionDepth.FiniteHenselFinal

namespace ApparitionDepth

/-! ## First-order derivative at the next finite level -/

/-- The derivative value of `X^d - 1` at `omega`, read in `ZMod (p^(r+1))`.

This is the finite-level version of

`d * omega^(d - 1)`.
-/
def finiteHenselDerivativeAtLevel (omega p d r : Nat) : ZMod (p ^ (r + 1)) :=
  (d : ZMod (p ^ (r + 1))) *
    (omega : ZMod (p ^ (r + 1))) ^ (d - 1)

/-- Unfolding helper for the finite-level derivative. -/
theorem finiteHenselDerivativeAtLevel_def (omega p d r : Nat) :
    finiteHenselDerivativeAtLevel omega p d r =
      (d : ZMod (p ^ (r + 1))) *
        (omega : ZMod (p ^ (r + 1))) ^ (d - 1) :=
  rfl

/-- The first-order binomial truncation certificate for one Hensel correction.

If `omegaNext` is connected to `omega` by the correction `t * p^r`, then the
intended finite congruence is

`omegaNext^d = omega^d + t*p^r*d*omega^(d-1)` in `ZMod (p^(r+1))`.

The proof that all higher binomial terms vanish modulo `p^(r+1)` is the
mathematical content isolated by this certificate. -/
def FiniteHenselBinomialTruncation
    (omega omegaNext t p d r : Nat) : Prop :=
  FiniteHenselStepRelation omega omegaNext t p r ∧
    ((omegaNext : ZMod (p ^ (r + 1))) ^ d =
      (omega : ZMod (p ^ (r + 1))) ^ d +
        ((t : ZMod (p ^ (r + 1))) *
          (p ^ r : ZMod (p ^ (r + 1)))) *
            finiteHenselDerivativeAtLevel omega p d r)

/-- Constructor for the binomial truncation certificate. -/
theorem finiteHenselBinomialTruncation_intro
    {omega omegaNext t p d r : Nat}
    (hstep : FiniteHenselStepRelation omega omegaNext t p r)
    (htrunc : (omegaNext : ZMod (p ^ (r + 1))) ^ d =
      (omega : ZMod (p ^ (r + 1))) ^ d +
        ((t : ZMod (p ^ (r + 1))) *
          (p ^ r : ZMod (p ^ (r + 1)))) *
            finiteHenselDerivativeAtLevel omega p d r) :
    FiniteHenselBinomialTruncation omega omegaNext t p d r :=
  ⟨hstep, htrunc⟩

/-- Projection: the correction step relation. -/
theorem finiteHenselBinomialTruncation_step
    {omega omegaNext t p d r : Nat}
    (h : FiniteHenselBinomialTruncation omega omegaNext t p d r) :
    FiniteHenselStepRelation omega omegaNext t p r :=
  h.1

/-- Projection: the first-order truncation equality. -/
theorem finiteHenselBinomialTruncation_eq
    {omega omegaNext t p d r : Nat}
    (h : FiniteHenselBinomialTruncation omega omegaNext t p d r) :
    (omegaNext : ZMod (p ^ (r + 1))) ^ d =
      (omega : ZMod (p ^ (r + 1))) ^ d +
        ((t : ZMod (p ^ (r + 1))) *
          (p ^ r : ZMod (p ^ (r + 1)))) *
            finiteHenselDerivativeAtLevel omega p d r :=
  h.2

/-- A binomial truncation certificate gives the previous-level reduction of the
candidate lift. -/
theorem finiteHenselBinomialTruncation_reduce
    {omega omegaNext t p d r : Nat}
    (h : FiniteHenselBinomialTruncation omega omegaNext t p d r) :
    (omegaNext : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) :=
  finiteHenselStepRelation_reduce (finiteHenselBinomialTruncation_step h)

/-- A binomial truncation certificate gives the correction formula at level
`p^(r+1)`. -/
theorem finiteHenselBinomialTruncation_formula
    {omega omegaNext t p d r : Nat}
    (h : FiniteHenselBinomialTruncation omega omegaNext t p d r) :
    (omegaNext : ZMod (p ^ (r + 1))) =
      (omega : ZMod (p ^ (r + 1))) +
        (t : ZMod (p ^ (r + 1))) *
          (p ^ r : ZMod (p ^ (r + 1))) :=
  finiteHenselStepRelation_formula (finiteHenselBinomialTruncation_step h)

end ApparitionDepth
