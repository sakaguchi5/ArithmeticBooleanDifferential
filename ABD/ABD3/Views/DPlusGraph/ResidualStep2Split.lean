import ABD.ABD3.Views.DPlusGraph.ResidualStep1Dominance

namespace ABD3

namespace ABCData

/-- Step 2 of the residual C-port argument, explicit-port form.

The positive C-port mass factors into accepted mass and unaccepted mass. -/
theorem residual_step2_cPortMassProductOnPorts_split
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.CPortMassProductOnPorts P =
      T.AcceptedCPortMassProduct P G R *
        T.UnacceptedCPortMassProduct P G R := by
  exact T.cPortMassProductOnPorts_eq_accepted_mul_unaccepted P G R

/-- Step 2 of the residual C-port argument, graph-language form. -/
theorem residual_step2_cPortMassProduct_split
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.CPortMassProduct P =
      T.AcceptedCPortMassProduct P G R *
        T.UnacceptedCPortMassProduct P G R := by
  exact T.cPortMassProduct_eq_accepted_mul_unaccepted P G R

end ABCData

end ABD3
