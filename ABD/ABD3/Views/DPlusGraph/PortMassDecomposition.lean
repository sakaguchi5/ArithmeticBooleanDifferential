import ABD.ABD3.Views.DPlusGraph.PortPartition

namespace ABD3

namespace ABCData

/-- The positive C-port mass splits into the mass carried by ports accepted by
A/B and the mass carried by the remaining unaccepted ports.

This is the product-level version of the `AcceptedCPorts` / `UnacceptedCPorts`
partition.  It is deliberately placed before the low-absorption contradiction
step: under low absorption the accepted factor becomes `1`, so the whole D+
C-port mass remains on the unaccepted side. -/
theorem cPortMassProductOnPorts_eq_accepted_mul_unaccepted
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.CPortMassProductOnPorts P =
      T.AcceptedCPortMassProduct P G R *
        T.UnacceptedCPortMassProduct P G R := by
  classical
  unfold CPortMassProductOnPorts AcceptedCPortMassProduct
    UnacceptedCPortMassProduct AcceptedCPorts UnacceptedCPorts
  exact (Finset.prod_filter_mul_prod_filter_not
    (s := T.CSurplusPorts P)
    (p := fun p => T.CPortAcceptedByAB P G R p)
    (f := fun p => p ^ T.PositiveSurplusExpAt P p)).symm

/-- The graph-language C-port mass splits into accepted and unaccepted C-port
mass. -/
theorem cPortMassProduct_eq_accepted_mul_unaccepted
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.CPortMassProduct P =
      T.AcceptedCPortMassProduct P G R *
        T.UnacceptedCPortMassProduct P G R := by
  rw [T.cPortMassProduct_eq_cPortMassProductOnPorts P]
  exact T.cPortMassProductOnPorts_eq_accepted_mul_unaccepted P G R

/-- Under low absorption, every bit of C-port mass is left on the unaccepted
side. -/
theorem cPortMassProductOnPorts_eq_unaccepted_of_cPortAbsorptionLow
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hlow : T.CPortAbsorptionLow P G R) :
    T.CPortMassProductOnPorts P = T.UnacceptedCPortMassProduct P G R := by
  rw [T.cPortMassProductOnPorts_eq_accepted_mul_unaccepted P G R,
    T.acceptedCPortMassProduct_eq_one_of_cPortAbsorptionLow P G R hlow,
    one_mul]

/-- Under low absorption, the graph-language C-port mass equals the unaccepted
mass. -/
theorem cPortMassProduct_eq_unaccepted_of_cPortAbsorptionLow
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hlow : T.CPortAbsorptionLow P G R) :
    T.CPortMassProduct P = T.UnacceptedCPortMassProduct P G R := by
  rw [T.cPortMassProduct_eq_cPortMassProductOnPorts P]
  exact T.cPortMassProductOnPorts_eq_unaccepted_of_cPortAbsorptionLow P G R hlow

/-- If no arithmetic edge is accepted, the whole C-port mass is unaccepted. -/
theorem cPortMassProductOnPorts_eq_unaccepted_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.CPortMassProductOnPorts P = T.UnacceptedCPortMassProduct P G R := by
  exact T.cPortMassProductOnPorts_eq_unaccepted_of_cPortAbsorptionLow
    P G R (T.cPortAbsorptionLow_of_noAcceptedArithmeticEdge P G R hno)

/-- If no arithmetic edge is accepted, the graph-language C-port mass equals the
unaccepted mass. -/
theorem cPortMassProduct_eq_unaccepted_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.CPortMassProduct P = T.UnacceptedCPortMassProduct P G R := by
  exact T.cPortMassProduct_eq_unaccepted_of_cPortAbsorptionLow
    P G R (T.cPortAbsorptionLow_of_noAcceptedArithmeticEdge P G R hno)

/-- In the low-absorption frontier, D+ dominance can be read entirely on the
unaccepted C-port mass.  This is the final bookkeeping bridge before the real
low-absorption contradiction argument. -/
theorem unacceptedCPortMassProduct_dominates_deficit_of_cPortMassDominatesDeficit_of_low
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hdom : T.CPortMassDominatesDeficit P)
    (hlow : T.CPortAbsorptionLow P G R) :
    T.NegativeDeficitProduct P < T.UnacceptedCPortMassProduct P G R := by
  unfold CPortMassDominatesDeficit at hdom
  rwa [T.cPortMassProduct_eq_unaccepted_of_cPortAbsorptionLow P G R hlow] at hdom

/-- If no arithmetic edge is accepted, D+ dominance is entirely carried by the
unaccepted C-port mass. -/
theorem unacceptedCPortMassProduct_dominates_deficit_of_cPortMassDominatesDeficit_of_noAccepted
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hdom : T.CPortMassDominatesDeficit P)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.NegativeDeficitProduct P < T.UnacceptedCPortMassProduct P G R := by
  exact T.unacceptedCPortMassProduct_dominates_deficit_of_cPortMassDominatesDeficit_of_low
    P G R hdom (T.cPortAbsorptionLow_of_noAcceptedArithmeticEdge P G R hno)

end ABCData

end ABD3
