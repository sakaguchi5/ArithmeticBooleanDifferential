import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step16ExternalBranchAxioms

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Final residual hard-core package for the pure two-power desync frontier.

This is stronger than just `Odd F.u ∧ Odd F.v`: it carries the original
`NormalForm`, the hard elementary layer, the residue toolkit, the external
closures of all non-both-odd branches, and the Branch 5 data.  This is the
single object that future work should attack by contradiction. -/
structure BothOddResidualHardCore (F : NormalForm T P) where
  external_closures : ExternalBranchClosureAxioms F
  branch5 : Branch5Data F
  package : Branch5Package F
  residues : Branch5ResidueToolkit F

/-- Build the residual hard core from the external branch closures. -/
def bothOddResidualHardCore_of_externalBranchClosureAxioms
    (F : NormalForm T P) (E : ExternalBranchClosureAxioms F) :
    BothOddResidualHardCore F :=
  let B : Branch5Data F := F.branch5Data_of_externalBranchClosureAxioms E
  { external_closures := E
    branch5 := B
    package := F.branch5Package_of_branch5Data B
    residues := F.branch5ResidueToolkit B }

/-- Canonical residual hard core using the named external inputs. -/
def bothOddResidualHardCore
    (F : NormalForm T P) :
    BothOddResidualHardCore F :=
  F.bothOddResidualHardCore_of_externalBranchClosureAxioms
    (F.externalBranchClosureAxioms)

/-- The residual hard core retains the source equation `p^u+q^v=2^w`. -/
theorem source_sum_eq_two_pow_of_bothOddResidualHardCore
    (F : NormalForm T P) (_K : BothOddResidualHardCore F) :
    F.p ^ F.u + F.q ^ F.v = 2 ^ F.w :=
  F.source_sum_eq_two_pow

/-- The residual hard core retains exponent coprimality. -/
theorem coprime_of_bothOddResidualHardCore
    (F : NormalForm T P) (K : BothOddResidualHardCore F) :
    Nat.Coprime F.u F.v :=
  F.branch5Package_coprime K.package

/-- The residual hard core has odd A-exponent. -/
theorem u_odd_of_bothOddResidualHardCore
    (F : NormalForm T P) (K : BothOddResidualHardCore F) :
    Odd F.u :=
  K.branch5.u_odd

/-- The residual hard core has odd B-exponent. -/
theorem v_odd_of_bothOddResidualHardCore
    (F : NormalForm T P) (K : BothOddResidualHardCore F) :
    Odd F.v :=
  K.branch5.v_odd

/-- The residual hard core has `3 ≤ u`. -/
theorem three_le_u_of_bothOddResidualHardCore
    (F : NormalForm T P) (K : BothOddResidualHardCore F) :
    3 ≤ F.u :=
  K.branch5.three_le_u

/-- The residual hard core has `3 ≤ v`. -/
theorem three_le_v_of_bothOddResidualHardCore
    (F : NormalForm T P) (K : BothOddResidualHardCore F) :
    3 ≤ F.v :=
  K.branch5.three_le_v

/-- The residual hard core has the mod-8 base constraint `p+q ≡ 0`. -/
theorem p_add_q_mod8_eq_zero_of_bothOddResidualHardCore
    (F : NormalForm T P) (K : BothOddResidualHardCore F) :
    (F.p + F.q) % 8 = 0 :=
  F.branch5Package_mod8 K.package

/-- The residual hard core closes the low-exponent branch. -/
theorem not_linearExponentBranch_of_bothOddResidualHardCore
    (F : NormalForm T P) (K : BothOddResidualHardCore F) :
    ¬ F.LinearExponentBranch :=
  F.no_linearExponentBranch_of_externalBranchClosureAxioms K.external_closures

/-- The residual hard core closes the mixed-parity branch. -/
theorem not_mixedParityBranch_of_bothOddResidualHardCore
    (F : NormalForm T P) (K : BothOddResidualHardCore F) :
    ¬ F.MixedParityBranch :=
  F.no_mixedParityBranch_of_externalBranchClosureAxioms K.external_closures

/-- The residual hard core closes the common-prime-exponent branch. -/
theorem not_commonPrimeExponentBranch_of_bothOddResidualHardCore
    (F : NormalForm T P) (_K : BothOddResidualHardCore F) :
    ¬ F.CommonPrimeExponentBranch :=
  F.no_commonPrimeExponentBranch

/-- The residual hard core retains the arbitrary-modulus source congruence. -/
theorem source_mod_of_bothOddResidualHardCore
    (F : NormalForm T P) (K : BothOddResidualHardCore F) (m : ℕ) :
    F.SourceSumModGoal m :=
  F.source_mod_of_branch5ResidueToolkit K.residues m

/-- The residual hard core retains the mod-3 source congruence. -/
theorem source_mod3_of_bothOddResidualHardCore
    (F : NormalForm T P) (K : BothOddResidualHardCore F) :
    F.SourceSumModThreeGoal :=
  F.source_mod3_of_branch5ResidueToolkit K.residues

/-- The residual hard core retains the mod-5 source congruence. -/
theorem source_mod5_of_bothOddResidualHardCore
    (F : NormalForm T P) (K : BothOddResidualHardCore F) :
    F.SourceSumModFiveGoal :=
  F.source_mod5_of_branch5ResidueToolkit K.residues

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
