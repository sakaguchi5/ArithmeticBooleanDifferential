import ABD.ABD3.Views.DPlusGraph.ResidualStep7RejectedNormalForm

namespace ABD3

namespace ABCData

/-- Step 7 concrete support-small normal form.

At the current ABD3 graph layer, support-small is the conservative frontier
`supportABC.card ≤ 3`.  Step 7 gives it a local name so later files can refine
or replace the threshold without changing the residual-dominance pipeline. -/
def ResidualSupportSmallConcrete
    (T : ABCData) (_P : PowerData)
    (_G : ArithmeticSyncGenerators) (_R : ℕ) : Prop :=
  T.supportABC.card ≤ 3

/-- The Step 7 concrete form is exactly the existing support-small exceptional
side. -/
theorem residualSupportSmallConcrete_iff_supportSmallExceptional
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.ResidualSupportSmallConcrete P G R ↔ T.SupportSmallExceptional := by
  rfl

/-- Concrete support-small gives the residual support-small frontier. -/
theorem residualSupportSmall_of_concrete
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ResidualSupportSmallConcrete P G R) :
    T.ResidualSupportSmall P G R := by
  exact h

/-- Residual support-small is currently the same as the concrete support-small
normal form. -/
theorem residualSupportSmallConcrete_of_residualSupportSmall
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ResidualSupportSmall P G R) :
    T.ResidualSupportSmallConcrete P G R := by
  exact h

/-- Concrete support-small triples lie in the residual frontier. -/
theorem residualFrontier_of_supportSmallConcrete
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ResidualSupportSmallConcrete P G R) :
    T.ResidualFrontier P G R := by
  exact T.residualFrontier_of_supportSmall P G R h

/-- Concrete support-small triples are graph-exceptional. -/
theorem dPlusGraphExceptional_of_supportSmallConcrete
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ResidualSupportSmallConcrete P G R) :
    T.DPlusGraphExceptional P := by
  exact T.dPlusGraphExceptional_of_residualFrontier P G R
    (T.residualFrontier_of_supportSmallConcrete P G R h)

/-- Outside the graph-exceptional side, the Step 7 support-small concrete frontier
is impossible. -/
theorem not_residualSupportSmallConcrete_of_not_dPlusGraphExceptional
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hnot : ¬ T.DPlusGraphExceptional P) :
    ¬ T.ResidualSupportSmallConcrete P G R := by
  intro hsmall
  exact hnot (T.dPlusGraphExceptional_of_supportSmallConcrete P G R hsmall)

/-- Step 7 exposes the remaining non-small-support side as a reusable predicate. -/
def ResidualSupportNotSmallConcrete
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ¬ T.ResidualSupportSmallConcrete P G R

/-- Non-exceptionality gives the non-small-support side. -/
theorem residualSupportNotSmallConcrete_of_not_dPlusGraphExceptional
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hnot : ¬ T.DPlusGraphExceptional P) :
    T.ResidualSupportNotSmallConcrete P G R := by
  exact T.not_residualSupportSmallConcrete_of_not_dPlusGraphExceptional P G R hnot

end ABCData

end ABD3
