import ABD.ABD3.Views.Valuation

namespace ABD3

/-- A block preimage-cost predicate.

`cost t B` means: the block linear form realizes scalar `t` with bound `B`.
ABD3 keeps this abstract; ABD2 supplies concrete versions through the bridge. -/
abbrev PreimageCost := ℤ → ℤ → Prop

/-- Common-scalar preimage cost shared by two block costs. -/
def CommonScalarPreimageCostAtMost
    (leftCost rightCost : PreimageCost)
    (rightTarget : ℤ → ℤ)
    (t B : ℤ) : Prop :=
  leftCost t B ∧ rightCost (rightTarget t) B

/-- Abstract D1 shape: A/B common scalar cancellation, `A=t`, `B=-t`. -/
def D1CommonScalarShape
    (ACost BCost : PreimageCost) (t B : ℤ) : Prop :=
  CommonScalarPreimageCostAtMost ACost BCost (fun t => -t) t B

/-- Abstract D2 shape: active/C common scalar forced lift, `active=t`, `C=t`. -/
def D2CommonScalarShape
    (ActiveCost CCost : PreimageCost) (t B : ℤ) : Prop :=
  CommonScalarPreimageCostAtMost ActiveCost CCost (fun t => t) t B

namespace ABCData

/-- ABD3-level interface for common-scalar analysis.

This is intentionally only an interface: it records the costs that ABD2 already
knows how to build, without importing ABD2 into the radical-analysis core. -/
structure CommonScalarCostInterface (_T : ABCData) where
  ACost : PreimageCost
  BCost : PreimageCost
  CCost : PreimageCost

/-- D1 common-scalar coverage through an interface. -/
def D1CoverageVia
    (T : ABCData) (_P : PowerData) (I : T.CommonScalarCostInterface) : Prop :=
  ∃ t B : ℤ,
    0 ≤ B ∧
    I.ACost t B ∧
    I.BCost (-t) B

/-- D2 common-scalar coverage through an interface, with an abstract active side. -/
def D2CoverageVia
    (T : ABCData) (_P : PowerData) (I : T.CommonScalarCostInterface) : Prop :=
  ∃ t B : ℤ,
    0 ≤ B ∧
    ((I.ACost t B ∨ I.BCost t B) ∧ I.CCost t B)

/-- ABD3 coverage shape: either A/B cancellation or active/C forced lift. -/
def CommonScalarCoverageVia
    (T : ABCData) (P : PowerData) (I : T.CommonScalarCostInterface) : Prop :=
  T.D1CoverageVia P I ∨ T.D2CoverageVia P I

end ABCData
end ABD3
