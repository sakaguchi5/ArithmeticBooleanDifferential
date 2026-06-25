import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step19ExternalFinitenessInputs

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- A residual candidate after a chosen killable part has been removed.

`Killable` is intentionally a parameter.  This lets the development add new
finite or empty families without rewriting the hard-core object: enlarge
`Killable`, and the residual core gets thinner. -/
structure BothOddResidualAfterKillable
    (Killable : Branch5Family T P)
    (F : NormalForm T P) (K : BothOddResidualHardCore F) : Prop where
  not_killable : ¬ Killable F K

/-- Extract the negated membership in the chosen killable part. -/
theorem not_killable_of_bothOddResidualAfterKillable
    {Killable : Branch5Family T P}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (R : BothOddResidualAfterKillable (T := T) (P := P) Killable F K) :
    ¬ Killable F K :=
  R.not_killable

/-- If a candidate avoids `A ∪ B`, then it avoids `A`. -/
theorem not_left_of_residualAfter_or
    {A B : Branch5Family T P}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (R : BothOddResidualAfterKillable
      (T := T) (P := P) (Branch5Family.or (T := T) (P := P) A B) F K) :
    ¬ A F K := by
  intro hA
  exact R.not_killable (Or.inl hA)

/-- If a candidate avoids `A ∪ B`, then it avoids `B`. -/
theorem not_right_of_residualAfter_or
    {A B : Branch5Family T P}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (R : BothOddResidualAfterKillable
      (T := T) (P := P) (Branch5Family.or (T := T) (P := P) A B) F K) :
    ¬ B F K := by
  intro hB
  exact R.not_killable (Or.inr hB)

/-- If a candidate avoids an indexed union, then it avoids every registered
member of that union. -/
theorem not_member_of_residualAfter_iUnion
    {ι : Sort _} {A : ι → Branch5Family T P}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (R : BothOddResidualAfterKillable
      (T := T) (P := P) (Branch5Family.iUnion (T := T) (P := P) A) F K)
    (i : ι) :
    ¬ A i F K := by
  intro hAi
  exact R.not_killable ⟨i, hAi⟩

/-- A residual candidate still carries the original both-odd hard core. -/
theorem source_sum_eq_two_pow_of_residualAfterKillable
    {Killable : Branch5Family T P}
    (F : NormalForm T P) (K : BothOddResidualHardCore F)
    (_R : BothOddResidualAfterKillable (T := T) (P := P) Killable F K) :
    F.p ^ F.u + F.q ^ F.v = 2 ^ F.w :=
  F.source_sum_eq_two_pow_of_bothOddResidualHardCore K

/-- A residual candidate still has the Branch 5 mod-8 constraint. -/
theorem mod8_of_residualAfterKillable
    {Killable : Branch5Family T P}
    (F : NormalForm T P) (K : BothOddResidualHardCore F)
    (_R : BothOddResidualAfterKillable (T := T) (P := P) Killable F K) :
    (F.p + F.q) % 8 = 0 :=
  F.p_add_q_mod8_eq_zero_of_bothOddResidualHardCore K

/-- A residual candidate still has arbitrary-modulus source congruences. -/
theorem source_mod_of_residualAfterKillable
    {Killable : Branch5Family T P}
    (F : NormalForm T P) (K : BothOddResidualHardCore F)
    (_R : BothOddResidualAfterKillable (T := T) (P := P) Killable F K)
    (m : ℕ) :
    F.SourceSumModGoal m :=
  F.source_mod_of_bothOddResidualHardCore K m

/-- A named predicate for the standard near-power killable part at a fixed scale. -/
def StandardNearPowerKillable
    (C : ℕ) : Branch5Family T P :=
  Branch5ScaleUnbalancedBy (T := T) (P := P) C

/-- A named predicate for the standard asymmetric-unbalanced killable part. -/
def StandardAsymmetricUnbalancedKillable
    (L C : ℕ) : Branch5Family T P :=
  Branch5AsymmetricUnbalancedBy (T := T) (P := P) L C

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
