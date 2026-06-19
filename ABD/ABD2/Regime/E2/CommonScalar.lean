import ABD.ABD2.Regime.E.Stage3Goals

namespace ABD2

/-- Common scalar-preimage cost.

This is the E2 normalization core.  It abstracts both D1 and D2 as follows:

* choose a nonzero scalar `t`;
* realize `t` on the left block;
* realize `rightTarget t` on the right block;
* aggregate the two component bounds into the ambient bound `B`.

D1 is obtained by `rightTarget t = -t`.
Pure D2-style common-value preimage problems use `rightTarget t = t`.
-/
def CommonScalarPreimageCostAtMost
    (leftCost rightCost : ℤ → ℤ → Prop)
    (rightTarget : ℤ → ℤ)
    (t B : ℤ) : Prop :=
  t ≠ 0 ∧
    ∃ BL BR : ℤ,
      leftCost t BL ∧
        rightCost (rightTarget t) BR ∧
          MaxAgg BL BR B

/-- Constructor for the common scalar-preimage cost. -/
theorem commonScalarPreimageCostAtMost_of_components
    {leftCost rightCost : ℤ → ℤ → Prop}
    {rightTarget : ℤ → ℤ}
    {t B BL BR : ℤ}
    (ht : t ≠ 0)
    (hleft : leftCost t BL)
    (hright : rightCost (rightTarget t) BR)
    (hagg : MaxAgg BL BR B) :
    CommonScalarPreimageCostAtMost leftCost rightCost rightTarget t B := by
  exact ⟨ht, BL, BR, hleft, hright, hagg⟩

/-- A common scalar-preimage cost is exactly its nonzero scalar and two
component preimage witnesses. -/
theorem commonScalarPreimageCostAtMost_iff
    (leftCost rightCost : ℤ → ℤ → Prop)
    (rightTarget : ℤ → ℤ)
    (t B : ℤ) :
    CommonScalarPreimageCostAtMost leftCost rightCost rightTarget t B ↔
      t ≠ 0 ∧
        ∃ BL BR : ℤ,
          leftCost t BL ∧
            rightCost (rightTarget t) BR ∧
              MaxAgg BL BR B := by
  rfl

/-- Rational power-saving packaging for a common scalar cost.

This is the E2 replacement for branch-specific Stage-3 goals: a chosen nonzero
scalar and an ambient bound must realize the common scalar cost and satisfy the
concrete rational power-saving inequality. -/
def CommonScalarPowerSavingEstimate
    (T : ABCTriple)
    (leftCost rightCost : ℤ → ℤ → Prop)
    (rightTarget : ℤ → ℤ)
    (data : ABCTriple.RationalPowerSavingData) : Prop :=
  ∃ t B : ℤ,
    0 ≤ B ∧
      B ^ data.N < ((T.c : ℤ) ^ data.M) ∧
        CommonScalarPreimageCostAtMost leftCost rightCost rightTarget t B

/-- Constructor for `CommonScalarPowerSavingEstimate`. -/
theorem commonScalarPowerSavingEstimate_of_bound
    (T : ABCTriple)
    {leftCost rightCost : ℤ → ℤ → Prop}
    {rightTarget : ℤ → ℤ}
    (data : ABCTriple.RationalPowerSavingData)
    {t B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : CommonScalarPreimageCostAtMost leftCost rightCost rightTarget t B) :
    CommonScalarPowerSavingEstimate T leftCost rightCost rightTarget data := by
  exact ⟨t, B, hBnonneg, hpow, hcost⟩

end ABD2
