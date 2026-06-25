import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step20ResidualAfterKillable

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- The two-adic source congruence at precision `2^k`. -/
def Branch5TwoAdicCongruenceAt
    (F : NormalForm T P) (_K : BothOddResidualHardCore F) (k : ℕ) : Prop :=
  F.SourceSumModGoal (2 ^ k)

/-- The Branch 5 two-adic congruence structure retained by the residual hard
core.  This is a deliberately lightweight hook for later 2-adic logarithm or
unit calculations. -/
structure Branch5TwoAdicDesyncStructure
    (F : NormalForm T P) (K : BothOddResidualHardCore F) : Prop where
  source_mod_two_pow : ∀ k : ℕ, Branch5TwoAdicCongruenceAt F K k

/-- Realize the lightweight two-adic structure from the arbitrary-modulus
residue toolkit already stored in `BothOddResidualHardCore`. -/
def branch5TwoAdicDesyncStructure
    (F : NormalForm T P) (K : BothOddResidualHardCore F) :
    Branch5TwoAdicDesyncStructure F K :=
  { source_mod_two_pow := fun k =>
      F.source_mod_of_bothOddResidualHardCore K (2 ^ k) }

/-- A residual candidate which is balanced and still carries the two-adic
congruence structure.

This is the next hard core after finite/empty killable families have been
removed.  The chosen `Killable` predicate is a parameter, so this core can be
made thinner by registering more killable families upstream. -/
structure BalancedTwoAdicDesyncCore
    (Killable : Branch5Family T P) (C : ℕ)
    (F : NormalForm T P) (K : BothOddResidualHardCore F) : Prop where
  residual : BothOddResidualAfterKillable (T := T) (P := P) Killable F K
  balanced : Branch5ScaleBalancedBy (T := T) (P := P) C F K
  two_adic : Branch5TwoAdicDesyncStructure F K

/-- Build the balanced two-adic core from a residual candidate and a balance
certificate. -/
def balancedTwoAdicDesyncCore_of_residual
    {Killable : Branch5Family T P} {C : ℕ}
    (F : NormalForm T P) (K : BothOddResidualHardCore F)
    (R : BothOddResidualAfterKillable (T := T) (P := P) Killable F K)
    (B : Branch5ScaleBalancedBy (T := T) (P := P) C F K) :
    BalancedTwoAdicDesyncCore (T := T) (P := P) Killable C F K :=
  { residual := R
    balanced := B
    two_adic := F.branch5TwoAdicDesyncStructure K }

/-- The final target shape for future work: prove that the balanced two-adic
residual core is contradictory for a sufficiently rich killable registry and a
chosen balance scale. -/
def BalancedTwoAdicDesyncContradictionGoal
    (Killable : Branch5Family T P) (C : ℕ) : Prop :=
  ∀ (F : NormalForm T P) (K : BothOddResidualHardCore F),
    BalancedTwoAdicDesyncCore (T := T) (P := P) Killable C F K → False

/-- The balanced two-adic core still has the original source equation. -/
theorem source_sum_eq_two_pow_of_balancedTwoAdicDesyncCore
    {Killable : Branch5Family T P} {C : ℕ}
    (F : NormalForm T P) (K : BothOddResidualHardCore F)
    (_R : BalancedTwoAdicDesyncCore (T := T) (P := P) Killable C F K) :
    F.p ^ F.u + F.q ^ F.v = 2 ^ F.w :=
  F.source_sum_eq_two_pow_of_bothOddResidualHardCore K

/-- The balanced two-adic core still has `p+q ≡ 0 mod 8`. -/
theorem mod8_of_balancedTwoAdicDesyncCore
    {Killable : Branch5Family T P} {C : ℕ}
    (F : NormalForm T P) (K : BothOddResidualHardCore F)
    (_R : BalancedTwoAdicDesyncCore (T := T) (P := P) Killable C F K) :
    (F.p + F.q) % 8 = 0 :=
  F.p_add_q_mod8_eq_zero_of_bothOddResidualHardCore K

/-- The balanced two-adic core exposes the two-adic congruence at every
precision `2^k`. -/
theorem twoAdicCongruence_of_balancedTwoAdicDesyncCore
    {Killable : Branch5Family T P} {C : ℕ}
    (F : NormalForm T P) (K : BothOddResidualHardCore F)
    (R : BalancedTwoAdicDesyncCore (T := T) (P := P) Killable C F K)
    (k : ℕ) :
    Branch5TwoAdicCongruenceAt F K k :=
  R.two_adic.source_mod_two_pow k

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
