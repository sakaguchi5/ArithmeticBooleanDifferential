/-
  ABD.ApparitionDepth.ZModFieldLinearSolve

  Step 21G of the Apparition-Depth Decomposition project.

  This file isolates the field-linear algebra needed for the Hensel correction
  equation.  The genuinely algebraic proof that a nonzero derivative in `ZMod p`
  gives a unique correction is represented by a small certificate, so later work
  can connect it to the appropriate mathlib field/finite-field API without
  changing the AD pipeline.
-/

import ABD.ApparitionDepth.BaseLevelUniqueness

namespace ApparitionDepth

/-! ## Linear solve certificates in `ZMod p` -/

/-- A field-linear solve certificate for equations

`q + t * a = 0` in `ZMod p`.

When `p` is prime and `a ≠ 0`, this should be proved by taking
`t = -q * a⁻¹`.  We keep it as a named certificate at this layer. -/
def ZModLinearSolveCertificate (p : Nat) (a : ZMod p) : Prop :=
  a ≠ 0 → ∀ q : Nat, FiniteHenselLinearSolved q p a

/-- A version where the nonzero condition is already supplied. -/
def ZModLinearSolveAtNonzero (p : Nat) (a : ZMod p) : Prop :=
  ∀ q : Nat, FiniteHenselLinearSolved q p a

/-- Constructor for the raw field-linear solve certificate. -/
theorem zmodLinearSolveCertificate_intro {p : Nat} {a : ZMod p}
    (h : a ≠ 0 → ∀ q : Nat, FiniteHenselLinearSolved q p a) :
    ZModLinearSolveCertificate p a :=
  h

/-- Apply a field-linear solve certificate. -/
theorem zmodLinearSolveCertificate_apply {p q : Nat} {a : ZMod p}
    (hcert : ZModLinearSolveCertificate p a)
    (ha : a ≠ 0) :
    FiniteHenselLinearSolved q p a :=
  hcert ha q

/-- Convert a certificate plus nonzero coefficient into the nonzero-specialized
form. -/
theorem zmodLinearSolveAtNonzero_of_certificate {p : Nat} {a : ZMod p}
    (hcert : ZModLinearSolveCertificate p a)
    (ha : a ≠ 0) :
    ZModLinearSolveAtNonzero p a :=
  fun q => zmodLinearSolveCertificate_apply (q := q) hcert ha

/-- Constructor for the nonzero-specialized linear solve data. -/
theorem zmodLinearSolveAtNonzero_intro {p : Nat} {a : ZMod p}
    (h : ∀ q : Nat, FiniteHenselLinearSolved q p a) :
    ZModLinearSolveAtNonzero p a :=
  h

/-- Apply nonzero-specialized linear solve data. -/
theorem zmodLinearSolveAtNonzero_apply {p q : Nat} {a : ZMod p}
    (h : ZModLinearSolveAtNonzero p a) :
    FiniteHenselLinearSolved q p a :=
  h q

/-- Branch-seed derivative version of the field-linear solve certificate. -/
def BranchSeedZModLinearSolveCertificate (g p d j : Nat) : Prop :=
  ZModLinearSolveCertificate p (branchSeedDerivativeValue g p d j)

/-- Concrete-representative derivative version of the field-linear solve
certificate. -/
def HenselDerivativeZModLinearSolveCertificate (omega p d : Nat) : Prop :=
  ZModLinearSolveCertificate p (branchDerivativeValue omega p d)

/-- Branch-seed derivative solve after the derivative is known to be nonzero. -/
theorem branchSeedLinearSolved_of_zmodCertificate
    {g q p d j : Nat}
    (hcert : BranchSeedZModLinearSolveCertificate g p d j)
    (hderiv : BranchSeedDerivativeNonzeroModP g p d j) :
    BranchSeedFiniteHenselLinearSolved g q p d j := by
  unfold BranchSeedZModLinearSolveCertificate at hcert
  unfold BranchSeedDerivativeNonzeroModP branchSeedDerivativeValue at hderiv
  exact zmodLinearSolveCertificate_apply (q := q) hcert hderiv

/-- Concrete derivative solve after the derivative is known to be nonzero. -/
theorem correctionLinearSolved_of_zmodCertificate
    {omega q p d : Nat}
    (hcert : HenselDerivativeZModLinearSolveCertificate omega p d)
    (hderiv : HenselDerivativeNonzeroModP omega p d) :
    FiniteHenselLinearSolved q p (branchDerivativeValue omega p d) := by
  unfold HenselDerivativeZModLinearSolveCertificate at hcert
  unfold HenselDerivativeNonzeroModP branchDerivativeValue at hderiv
  exact zmodLinearSolveCertificate_apply (q := q) hcert hderiv

end ApparitionDepth
