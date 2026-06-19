import ABD.ABD2.Cost.Core

namespace ABD2

universe u

/-- A bound aggregator combines two component bounds into one ambient bound. -/
abbrev BoundAggregator := ℤ → ℤ → ℤ → Prop

/-- The max-style aggregator, kept as a predicate to avoid committing to an actual
`max` expression too early.  It says both component bounds fit under `B`. -/
def MaxAgg : BoundAggregator :=
  fun B₁ B₂ B => B₁ ≤ B ∧ B₂ ≤ B

/-- Pair smallness induced by two component smallness predicates and an aggregator. -/
def PairSmall
    {V W : Type u}
    (smallV : V → ℤ → Prop) (smallW : W → ℤ → Prop)
    (agg : BoundAggregator)
    (x : V) (y : W) (B : ℤ) : Prop :=
  ∃ Bx By : ℤ,
    smallV x Bx ∧ smallW y By ∧ agg Bx By B

/-- Constructor for pair smallness. -/
theorem pairSmall_of_bounds
    {V W : Type u}
    {smallV : V → ℤ → Prop} {smallW : W → ℤ → Prop}
    {agg : BoundAggregator}
    {x : V} {y : W} {B Bx By : ℤ}
    (hx : smallV x Bx) (hy : smallW y By)
    (hagg : agg Bx By B) :
    PairSmall smallV smallW agg x y B := by
  exact ⟨Bx, By, hx, hy, hagg⟩

/-- Pair smallness for the max-style aggregator. -/
def PairSmallMax
    {V W : Type u}
    (smallV : V → ℤ → Prop) (smallW : W → ℤ → Prop)
    (x : V) (y : W) (B : ℤ) : Prop :=
  PairSmall smallV smallW MaxAgg x y B

/-- Constructor for max-style pair smallness. -/
theorem pairSmallMax_of_bounds
    {V W : Type u}
    {smallV : V → ℤ → Prop} {smallW : W → ℤ → Prop}
    {x : V} {y : W} {B Bx By : ℤ}
    (hx : smallV x Bx) (hy : smallW y By)
    (hBx : Bx ≤ B) (hBy : By ≤ B) :
    PairSmallMax smallV smallW x y B := by
  exact pairSmall_of_bounds hx hy ⟨hBx, hBy⟩

end ABD2
