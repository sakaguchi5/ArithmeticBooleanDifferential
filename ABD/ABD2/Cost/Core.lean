import ABD.ABD2.Fibration.TargetZeroCostAnatomy

namespace ABD2

universe u

/-- A generic preimage-cost predicate.

`BlockPreimageCostAtMost L small t B` means that the scalar target `t` is
realized by some block/vector whose size is accepted at bound `B`.

This is the C0 normalization layer: later branch costs should be phrased as
simultaneous preimage costs for the relevant block linear forms. -/
def BlockPreimageCostAtMost
    {V : Type u}
    (L : V → ℤ) (small : V → ℤ → Prop)
    (t B : ℤ) : Prop :=
  ∃ x : V, L x = t ∧ small x B

/-- The direct witness constructor for `BlockPreimageCostAtMost`. -/
theorem blockPreimageCostAtMost_of_witness
    {V : Type u} {L : V → ℤ} {small : V → ℤ → Prop}
    {t B : ℤ} {x : V}
    (hL : L x = t) (hsmall : small x B) :
    BlockPreimageCostAtMost L small t B := by
  exact ⟨x, hL, hsmall⟩

/-- Forget the realizing vector from a preimage-cost witness. -/
theorem exists_witness_of_blockPreimageCostAtMost
    {V : Type u} {L : V → ℤ} {small : V → ℤ → Prop}
    {t B : ℤ}
    (h : BlockPreimageCostAtMost L small t B) :
    ∃ x : V, L x = t ∧ small x B := by
  exact h

/-- A finite preimage-cost predicate for a scalar target. -/
def HasFiniteBlockPreimageCost
    {V : Type u}
    (L : V → ℤ) (small : V → ℤ → Prop)
    (t : ℤ) : Prop :=
  ∃ B : ℤ, BlockPreimageCostAtMost L small t B

/-- A witness at a concrete bound gives finite preimage cost. -/
theorem hasFiniteBlockPreimageCost_of_atMost
    {V : Type u} {L : V → ℤ} {small : V → ℤ → Prop}
    {t B : ℤ}
    (h : BlockPreimageCostAtMost L small t B) :
    HasFiniteBlockPreimageCost L small t := by
  exact ⟨B, h⟩

end ABD2
