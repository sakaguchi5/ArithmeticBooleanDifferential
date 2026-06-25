import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step15ResidueSignature

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- The completely linear low-exponent branch. -/
def LinearBothExponentBranch (F : NormalForm T P) : Prop :=
  F.u = 1 ∧ F.v = 1

/-- Exactly one of the two exponents is linear. -/
def ExactlyOneLinearExponentBranch (F : NormalForm T P) : Prop :=
  (F.u = 1 ∧ F.v ≠ 1) ∨ (F.u ≠ 1 ∧ F.v = 1)

/-- The mixed-parity branch with even two-adic exponent. -/
def MixedParityEvenWBranch (F : NormalForm T P) : Prop :=
  F.MixedParityBranch ∧ Even F.w

/-- The mixed-parity branch with odd two-adic exponent. -/
def MixedParityOddWBranch (F : NormalForm T P) : Prop :=
  F.MixedParityBranch ∧ Odd F.w

/-- A prime exponent common to both source exponents.

This branch is actually eliminated internally by `F.exponentCoprime`, but it is
kept as a named branch in the residual bookkeeping because it is part of the
mathematical case split leading to the both-odd hard core. -/
def CommonPrimeExponentBranch (F : NormalForm T P) : Prop :=
  ∃ ℓ : ℕ, Nat.Prime ℓ ∧ ℓ ∣ F.u ∧ ℓ ∣ F.v

/-- External input A: the `u=v=1` branch is incompatible with the pure two-power
radical-small/desync package. -/
axiom external_no_linearBothExponentBranch
    (F : NormalForm T P) :
    ¬ F.LinearBothExponentBranch

/-- External input B: the exactly-one-linear-exponent branch is finite/excluded
by Baker--Tijdeman/S-unit type input in the pure two-power desync setting. -/
axiom external_no_exactlyOneLinearExponentBranch
    (F : NormalForm T P) :
    ¬ F.ExactlyOneLinearExponentBranch

/-- External input C: the mixed-parity branch with even `w` is excluded by the
factorization/Catalan branch analysis, with the remaining small solution removed
by radical-smallness. -/
axiom external_no_mixedParityEvenWBranch
    (F : NormalForm T P) :
    ¬ F.MixedParityEvenWBranch

/-- External input D: the mixed-parity branch with odd `w` is finite/excluded by
the `ℤ[√2]` norm-equation and Lucas/Lehmer primitive-divisor branch analysis. -/
axiom external_no_mixedParityOddWBranch
    (F : NormalForm T P) :
    ¬ F.MixedParityOddWBranch

/-- Convenience package for all non-both-odd external closures. -/
structure ExternalBranchClosureAxioms (F : NormalForm T P) : Prop where
  no_linear_both : ¬ F.LinearBothExponentBranch
  no_exactly_one_linear : ¬ F.ExactlyOneLinearExponentBranch
  no_mixed_even_w : ¬ F.MixedParityEvenWBranch
  no_mixed_odd_w : ¬ F.MixedParityOddWBranch

/-- Realize the external branch-closure package from the named external inputs. -/
def externalBranchClosureAxioms
    (F : NormalForm T P) :
    ExternalBranchClosureAxioms F :=
  { no_linear_both := external_no_linearBothExponentBranch F
    no_exactly_one_linear := external_no_exactlyOneLinearExponentBranch F
    no_mixed_even_w := external_no_mixedParityEvenWBranch F
    no_mixed_odd_w := external_no_mixedParityOddWBranch F }

/-- The external low-exponent inputs imply that the linear-exponent branch is
closed. -/
theorem no_linearExponentBranch_of_externalBranchClosureAxioms
    (F : NormalForm T P) (E : ExternalBranchClosureAxioms F) :
    ¬ F.LinearExponentBranch := by
  intro hlin
  rcases hlin with hu1 | hv1
  · by_cases hv1 : F.v = 1
    · exact E.no_linear_both ⟨hu1, hv1⟩
    · exact E.no_exactly_one_linear (Or.inl ⟨hu1, hv1⟩)
  · by_cases hu1 : F.u = 1
    · exact E.no_linear_both ⟨hu1, hv1⟩
    · exact E.no_exactly_one_linear (Or.inr ⟨hu1, hv1⟩)

/-- External parity-case input, packaged at the level needed for the residual
hard-core reduction.

The two finer axioms above record the intended mathematical sources: even `w`
uses factorization/Catalan, while odd `w` uses the `ℤ[√2]` norm-equation and
Lucas/Lehmer primitive-divisor branch.  This aggregate axiom is the exact API
needed downstream: after the external closures, no mixed-parity survivor remains. -/
axiom external_no_mixedParityBranch
    (F : NormalForm T P) :
    ¬ F.MixedParityBranch

/-- Realize the aggregate mixed-parity closure. -/
theorem no_mixedParityBranch_of_externalBranchClosureAxioms
    (F : NormalForm T P) (_E : ExternalBranchClosureAxioms F) :
    ¬ F.MixedParityBranch :=
  external_no_mixedParityBranch F

/-- The common-prime-exponent branch is already internally closed by the
PureTwo3 exponent-coprimality theorem. -/
theorem no_commonPrimeExponentBranch
    (F : NormalForm T P) :
    ¬ F.CommonPrimeExponentBranch := by
  intro h
  rcases h with ⟨ℓ, hℓ_prime, hℓ_dvd_u, hℓ_dvd_v⟩
  exact F.no_common_prime_exponent_divisor hℓ_prime ⟨hℓ_dvd_u, hℓ_dvd_v⟩

/-- Residual branch reduction.

Once all non-both-odd branches are closed, the only surviving exponent branch is
Branch 5: both exponents are odd and at least `3`.  This is deliberately kept as
an axiom here so the next files can focus on the final hard core while later work
may replace this wrapper by an elementary parity/case-split proof. -/
axiom branch5Data_of_externalBranchClosureAxioms
    (F : NormalForm T P) (E : ExternalBranchClosureAxioms F) :
    Branch5Data F

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
