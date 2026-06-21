import ABD.ABD3.Views.DPlusGraph.ProductObstruction.Step1Input

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 2A.

The A-facing C-residual product over all positive C-surplus ports.

This is only a bookkeeping product.  The first robust lower bound is kept as the
pointwise predicate below, so later files can choose whether to turn it into a
literal finite-product inequality or a log/product-weighted inequality. -/
def CResidualProductAgainstA
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) : ℕ :=
  (T.CSurplusPorts P).prod
    (fun p => RightSyncResidualNat G.gA (T.CPortCoeffNat p))

/-- Product-obstruction route, Step 2B.

The B-facing C-residual product over all positive C-surplus ports. -/
def CResidualProductAgainstB
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) : ℕ :=
  (T.CSurplusPorts P).prod
    (fun p => RightSyncResidualNat G.gB (T.CPortCoeffNat p))

/-- The baseline product one would get if every C-residual factor is at least
`R + 1`. -/
def CResidualBaselineProduct
    (T : ABCData) (P : PowerData) (R : ℕ) : ℕ :=
  (T.CSurplusPorts P).prod (fun _p => R + 1)

/-- Pointwise lower-bound form for the A-facing residual product. -/
def CResidualProductLowerBoundAgainstA
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ∀ p, p ∈ T.CSurplusPorts P →
    R + 1 ≤ RightSyncResidualNat G.gA (T.CPortCoeffNat p)

/-- Pointwise lower-bound form for the B-facing residual product. -/
def CResidualProductLowerBoundAgainstB
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ∀ p, p ∈ T.CSurplusPorts P →
    R + 1 ≤ RightSyncResidualNat G.gB (T.CPortCoeffNat p)

/-- A right residual rejection gives the corresponding pointwise `R + 1` lower
bound. -/
theorem rightResidualLowerBound_of_rightResidualRejected
    {R x y : ℕ}
    (h : RightSyncResidualRejectedBy R x y) :
    R + 1 ≤ RightSyncResidualNat x y := by
  unfold RightSyncResidualRejectedBy at h
  omega

/-- Product-obstruction input gives the A-facing pointwise product lower bound. -/
theorem cResidualProductLowerBoundAgainstA_of_productObstructionInput
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionInput P G R) :
    T.CResidualProductLowerBoundAgainstA P G R := by
  intro p hp
  exact rightResidualLowerBound_of_rightResidualRejected
    (T.cResidualHighAgainstA_of_productObstructionInput P G R h hp)

/-- Product-obstruction input gives the B-facing pointwise product lower bound. -/
theorem cResidualProductLowerBoundAgainstB_of_productObstructionInput
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionInput P G R) :
    T.CResidualProductLowerBoundAgainstB P G R := by
  intro p hp
  exact rightResidualLowerBound_of_rightResidualRejected
    (T.cResidualHighAgainstB_of_productObstructionInput P G R h hp)

/-- Literal finite-product lower-bound goal for the A-facing residual product.

This is intentionally a named goal rather than the main Step 2 output.  The safe
output is the pointwise lower bound above; later steps can prove this product
version when the desired product API is fixed. -/
def CResidualProductAgainstALowerBoundGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CResidualBaselineProduct P R ≤ T.CResidualProductAgainstA P G

/-- Literal finite-product lower-bound goal for the B-facing residual product. -/
def CResidualProductAgainstBLowerBoundGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.CResidualBaselineProduct P R ≤ T.CResidualProductAgainstB P G

end ABCData

end ABD3
