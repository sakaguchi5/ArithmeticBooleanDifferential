/-
  ABD.ApparitionDepth.PrimeNeZeroBridge

  Step 21T of the Apparition-Depth Decomposition project.

  This file supplies the small bridge needed after the actual `ZMod` linear-solve
  proof: many downstream AD statements carry `[Fact p.Prime]`, while the concrete
  `ZMod` field proof asks for both `[NeZero p]` and `[Fact p.Prime]`.
-/

import ABD.ApparitionDepth.ZModLinearSolveActual

namespace ApparitionDepth

/-! ## From primality to `NeZero` -/

/-- A prime natural number is nonzero, as a `NeZero` instance. -/
theorem neZero_of_fact_prime (p : Nat) [Fact p.Prime] : NeZero p := by
  have hp_two : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp_pos : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hp_two
  exact ⟨ne_of_gt hp_pos⟩

/-- Run a proof needing `[NeZero p]` under a prime-modulus assumption. -/
def withNeZero_of_fact_prime {p : Nat} [Fact p.Prime] {P : Sort u}
    (h : NeZero p → P) : P :=
  h (neZero_of_fact_prime p)

/-! ## Linear-solve API without explicitly passing `[NeZero p]` -/

/-- Prime-modulus explicit linear solve, using only `[Fact p.Prime]` at the call site. -/
theorem zmodLinearExplicitSolveAtNonzero_of_factPrime
    {p : Nat} [Fact p.Prime] (a : ZMod p) :
    ZModLinearExplicitSolveAtNonzero p a := by
  haveI : NeZero p := neZero_of_fact_prime p
  exact zmodLinearExplicitSolveAtNonzero_of_prime a

/-- Prime-modulus solve certificate, using only `[Fact p.Prime]` at the call site. -/
theorem zmodLinearSolveCertificate_of_factPrime
    {p : Nat} [Fact p.Prime] (a : ZMod p) :
    ZModLinearSolveCertificate p a := by
  haveI : NeZero p := neZero_of_fact_prime p
  exact zmodLinearSolveCertificate_of_prime a

/-- Branch-seed derivative linear solve from primality alone. -/
theorem branchSeedZModLinearSolveCertificate_of_factPrime
    {g p d j : Nat} [Fact p.Prime] :
    BranchSeedZModLinearSolveCertificate g p d j := by
  haveI : NeZero p := neZero_of_fact_prime p
  exact branchSeedZModLinearSolveCertificate_of_prime

/-- Concrete derivative linear solve from primality alone. -/
theorem henselDerivativeZModLinearSolveCertificate_of_factPrime
    {omega p d : Nat} [Fact p.Prime] :
    HenselDerivativeZModLinearSolveCertificate omega p d := by
  haveI : NeZero p := neZero_of_fact_prime p
  exact henselDerivativeZModLinearSolveCertificate_of_prime

/-- Concrete correction solve from derivative nonvanishing and primality, without
requiring callers to provide `[NeZero p]` explicitly. -/
theorem finiteHenselCorrectionSolved_of_factPrime_derivativeNonzero
    {omega q p d : Nat} [Fact p.Prime]
    (hderiv : HenselDerivativeNonzeroModP omega p d) :
    FiniteHenselCorrectionSolved omega q p d := by
  haveI : NeZero p := neZero_of_fact_prime p
  exact finiteHenselCorrectionSolved_of_prime_derivativeNonzero hderiv

end ApparitionDepth
