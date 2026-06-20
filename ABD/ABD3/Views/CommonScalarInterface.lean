import ABD.ABD3.Views.Valuation

namespace ABD3

/-- A block preimage-cost predicate.

`cost t B` means: the block linear form realizes scalar `t` with bound `B`.
ABD3 keeps this abstract; ABD2 supplies concrete versions through the bridge. -/
abbrev PreimageCost := ℤ → ℤ → Prop

namespace CommonScalar

/-- Common-scalar preimage cost shared by two block costs. -/
def PreimageCostAtMost
    (leftCost rightCost : PreimageCost)
    (rightTarget : ℤ → ℤ)
    (t B : ℤ) : Prop :=
  leftCost t B ∧ rightCost (rightTarget t) B

/-- Abstract D1 shape: A/B common scalar cancellation, `A=t`, `B=-t`. -/
def D1Shape
    (ACost BCost : PreimageCost) (t B : ℤ) : Prop :=
  PreimageCostAtMost ACost BCost (fun t => -t) t B

/-- Abstract D2 shape: active/C common scalar forced lift, `active=t`, `C=t`. -/
def D2Shape
    (ActiveCost CCost : PreimageCost) (t B : ℤ) : Prop :=
  PreimageCostAtMost ActiveCost CCost (fun t => t) t B

/-- ABD3-level interface for common-scalar analysis.

This records block preimage costs supplied from ABD2-side facts,
without importing ABD2 into the radical-analysis core.
-/
structure CostInterface (_T : ABCData) where
  ACost : PreimageCost
  BCost : PreimageCost
  CCost : PreimageCost

/-- Power bound against an externally supplied height scale. -/
def PowerBound (P : PowerData) (height B : ℤ) : Prop :=
  0 ≤ B ∧ B ^ P.N < height ^ P.M

/-- D1 route: A/B realize opposite nonzero scalar values. -/
def D1CoverageVia
    (T : ABCData) (P : PowerData) (height : ℤ)
    (I : CostInterface T) : Prop :=
  ∃ t B : ℤ,
    t ≠ 0 ∧
    PowerBound P height B ∧
    D1Shape I.ACost I.BCost t B

/-- D2 route: active A/B side and C realize the same nonzero scalar value. -/
def D2CoverageVia
    (T : ABCData) (P : PowerData) (height : ℤ)
    (I : CostInterface T) : Prop :=
  ∃ t B : ℤ,
    t ≠ 0 ∧
    PowerBound P height B ∧
    (D2Shape I.ACost I.CCost t B ∨
     D2Shape I.BCost I.CCost t B)

/-- Common-scalar coverage: either D1 or D2 succeeds. -/
def CoverageVia
    (T : ABCData) (P : PowerData) (height : ℤ)
    (I : CostInterface T) : Prop :=
  D1CoverageVia T P height I ∨ D2CoverageVia T P height I

def CoverageAtCHeight
    (T : ABCData) (P : PowerData)
    (I : CommonScalar.CostInterface T) : Prop :=
  CommonScalar.CoverageVia T P (T.C : ℤ) I

end CommonScalar
end ABD3
