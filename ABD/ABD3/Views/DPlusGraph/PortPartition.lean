import ABD.ABD3.Views.DPlusGraph.PortProduct

namespace ABD3

namespace ABCData

/-- A positive C-port is accepted by the A/B side when either A-C or B-C
synchronization is cheap. -/
def CPortAcceptedByAB
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  T.CPortAbsorbedByA P G R p ∨ T.CPortAbsorbedByB P G R p

/-- Positive C-ports that are accepted by A or B. -/
noncomputable def AcceptedCPorts
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Finset ℕ := by
  classical
  exact (T.CSurplusPorts P).filter
    (fun p => T.CPortAcceptedByAB P G R p)

/-- Positive C-ports that are not accepted by either A or B. -/
noncomputable def UnacceptedCPorts
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Finset ℕ := by
  classical
  exact (T.CSurplusPorts P).filter
    (fun p => ¬ T.CPortAcceptedByAB P G R p)

/-- Mass carried by accepted positive C-ports. -/
noncomputable def AcceptedCPortMassProduct
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : ℕ :=
  (T.AcceptedCPorts P G R).prod (fun p => p ^ T.PositiveSurplusExpAt P p)

/-- Mass carried by unaccepted positive C-ports. -/
noncomputable def UnacceptedCPortMassProduct
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : ℕ :=
  (T.UnacceptedCPorts P G R).prod (fun p => p ^ T.PositiveSurplusExpAt P p)

@[simp] theorem mem_acceptedCPorts_iff
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) :
    p ∈ T.AcceptedCPorts P G R ↔
      p ∈ T.CSurplusPorts P ∧ T.CPortAcceptedByAB P G R p := by
  simp [AcceptedCPorts]

@[simp] theorem mem_unacceptedCPorts_iff
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) :
    p ∈ T.UnacceptedCPorts P G R ↔
      p ∈ T.CSurplusPorts P ∧ ¬ T.CPortAcceptedByAB P G R p := by
  simp [UnacceptedCPorts]

@[simp] theorem mem_AcceptedCPorts_iff_absorbed
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ) :
    p ∈ T.AcceptedCPorts P G R ↔
      p ∈ T.CSurplusPorts P ∧
        (T.CPortAbsorbedByA P G R p ∨
         T.CPortAbsorbedByB P G R p) := by
  classical
  simp [AcceptedCPorts, CPortAcceptedByAB]

/-- Low absorption leaves no accepted positive C-ports. -/
theorem acceptedCPorts_eq_empty_of_cPortAbsorptionLow
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hlow : T.CPortAbsorptionLow P G R) :
    T.AcceptedCPorts P G R = ∅ := by
  ext p
  constructor
  · intro hp
    have hmem := (T.mem_acceptedCPorts_iff P G R p).mp hp
    rcases hmem with ⟨hpPort, hacc⟩
    have hun : T.CPortUnabsorbedAt P G R p :=
      T.cPortUnabsorbedAt_of_absorptionLow P G R hlow hpPort
    rcases hacc with hA | hB
    · exact False.elim ((T.not_cPortAbsorbedByA_of_unabsorbed P G R hun) hA)
    · exact False.elim ((T.not_cPortAbsorbedByB_of_unabsorbed P G R hun) hB)
  · intro hp
    simp at hp

/-- Under low absorption, the accepted C-port mass is trivial. -/
theorem acceptedCPortMassProduct_eq_one_of_cPortAbsorptionLow
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hlow : T.CPortAbsorptionLow P G R) :
    T.AcceptedCPortMassProduct P G R = 1 := by
  unfold AcceptedCPortMassProduct
  rw [T.acceptedCPorts_eq_empty_of_cPortAbsorptionLow P G R hlow]
  simp

/-- No accepted arithmetic edge also leaves no accepted positive C-port mass. -/
theorem acceptedCPortMassProduct_eq_one_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hno : T.NoAcceptedArithmeticEdge P G R) :
    T.AcceptedCPortMassProduct P G R = 1 := by
  exact T.acceptedCPortMassProduct_eq_one_of_cPortAbsorptionLow
    P G R (T.cPortAbsorptionLow_of_noAcceptedArithmeticEdge P G R hno)

/-- Under low absorption, every positive C-port lies in the unaccepted side. -/
theorem cSurplusPorts_subset_unacceptedCPorts_of_cPortAbsorptionLow
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hlow : T.CPortAbsorptionLow P G R) :
    T.CSurplusPorts P ⊆ T.UnacceptedCPorts P G R := by
  intro p hpPort
  refine (T.mem_unacceptedCPorts_iff P G R p).mpr ⟨hpPort, ?_⟩
  have hun : T.CPortUnabsorbedAt P G R p :=
    T.cPortUnabsorbedAt_of_absorptionLow P G R hlow hpPort
  intro hacc
  rcases hacc with hA | hB
  · exact (T.not_cPortAbsorbedByA_of_unabsorbed P G R hun) hA
  · exact (T.not_cPortAbsorbedByB_of_unabsorbed P G R hun) hB

end ABCData

end ABD3
