import ABD.ABD3.Views.DPlusGraph.ResidualStep2Split

namespace ABD3

namespace ABCData

/-- Step 3 of the residual C-port argument.

Under low C-port absorption, accepted C-port mass is trivial. -/
theorem residual_step3_acceptedMass_eq_one_of_lowAbsorption
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hlow : T.CPortAbsorptionLow P G R) :
    T.AcceptedCPortMassProduct P G R = 1 := by
  exact T.acceptedCPortMassProduct_eq_one_of_cPortAbsorptionLow P G R hlow

/-- Step 3, no-accepted-edge version.

If no arithmetic edge is accepted, accepted C-port mass is trivial. -/
theorem residual_step3_acceptedMass_eq_one_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.AcceptedCPortMassProduct P G R = 1 := by
  exact T.acceptedCPortMassProduct_eq_one_of_noAcceptedArithmeticEdge P G R hno

/-- Step 3, explicit-port form.

If no arithmetic edge is accepted, all C-port mass lies on the unaccepted side. -/
theorem residual_step3_cPortMassProductOnPorts_eq_unaccepted_of_noAccepted
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.CPortMassProductOnPorts P = T.UnacceptedCPortMassProduct P G R := by
  exact T.cPortMassProductOnPorts_eq_unaccepted_of_noAcceptedArithmeticEdge
    P G R hno

/-- Step 3, graph-language form.

If no arithmetic edge is accepted, total C-port mass equals unaccepted C-port
mass. -/
theorem residual_step3_cPortMassProduct_eq_unaccepted_of_noAccepted
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.CPortMassProduct P = T.UnacceptedCPortMassProduct P G R := by
  exact T.cPortMassProduct_eq_unaccepted_of_noAcceptedArithmeticEdge P G R hno

end ABCData

end ABD3
