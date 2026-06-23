import ABD.ABD3.Views.CollisionFrontierPureTwo2.Step8CSurplusPorts

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo2
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Concrete three-edge desynchronization normal form for the pure two-power model. -/
def ThreeRejections (F : NormalForm T P) (R : ℕ) : Prop :=
  SyncRejectedBy R F.pureGA F.pureGB ∧
    SyncRejectedBy R F.pureGA F.pureGC ∧
      SyncRejectedBy R F.pureGB F.pureGC

/-- No accepted arithmetic edge implies the three explicit rejections, once the
positive C-surplus ports have been identified as `{2}`. -/
theorem threeRejections_of_noAcceptedArithmeticEdge_of_ports
    (F : NormalForm T P) (R : ℕ)
    (hports : T.CSurplusPorts P = {2})
    (hno : T.NoAcceptedArithmeticEdge P F.pureSyncGenerators R) :
    F.ThreeRejections R := by
  constructor
  · simpa [ThreeRejections, pureSyncGenerators, ABEdgeRejected]
      using hno.1
  · constructor
    · have hmem : 2 ∈ T.CSurplusPorts P := by
        rw [hports]
        simp
      have hun : T.CPortUnabsorbedAt P F.pureSyncGenerators R 2 :=
        T.cPortUnabsorbedAt_of_absorptionLow P F.pureSyncGenerators R hno.2 hmem
      simpa [ThreeRejections, pureSyncGenerators, F.cPortCoeffNat_two_eq_pureGC]
        using hun.2.1
    · have hmem : 2 ∈ T.CSurplusPorts P := by
        rw [hports]
        simp
      have hun : T.CPortUnabsorbedAt P F.pureSyncGenerators R 2 :=
        T.cPortUnabsorbedAt_of_absorptionLow P F.pureSyncGenerators R hno.2 hmem
      simpa [ThreeRejections, pureSyncGenerators, F.cPortCoeffNat_two_eq_pureGC]
        using hun.2.2

/-- The three explicit rejections imply no accepted arithmetic edge, once the
positive C-surplus ports have been identified as `{2}`. -/
theorem noAcceptedArithmeticEdge_of_threeRejections_of_ports
    (F : NormalForm T P) (R : ℕ)
    (hports : T.CSurplusPorts P = {2})
    (hthree : F.ThreeRejections R) :
    T.NoAcceptedArithmeticEdge P F.pureSyncGenerators R := by
  refine ⟨?_, ?_⟩
  · simpa [ThreeRejections, pureSyncGenerators, ABEdgeRejected]
      using hthree.1
  · intro port hport
    have hmem_single : port ∈ ({2} : Finset ℕ) := by
      simpa [hports] using hport
    have hport_eq : port = 2 := by
      simpa using hmem_single
    subst port
    refine ⟨?_, ?_, ?_⟩
    · rw [hports]
      simp
    · simpa [ThreeRejections, pureSyncGenerators, F.cPortCoeffNat_two_eq_pureGC]
        using hthree.2.1
    · simpa [ThreeRejections, pureSyncGenerators, F.cPortCoeffNat_two_eq_pureGC]
        using hthree.2.2

/-- Port-level equivalence between the abstract ABD3 no-accepted-edge predicate
and the concrete three-edge rejection predicate. -/
theorem noAcceptedArithmeticEdge_iff_threeRejections_of_ports
    (F : NormalForm T P) (R : ℕ)
    (hports : T.CSurplusPorts P = {2}) :
    T.NoAcceptedArithmeticEdge P F.pureSyncGenerators R ↔ F.ThreeRejections R := by
  constructor
  · exact F.threeRejections_of_noAcceptedArithmeticEdge_of_ports R hports
  · exact F.noAcceptedArithmeticEdge_of_threeRejections_of_ports R hports

/-- Main Step 9 output: under radical-smallness, Step 8 supplies
`CSurplusPorts = {2}`, so the abstract no-accepted-edge predicate is exactly the
three concrete rejections `A-B`, `A-C₂`, and `B-C₂`. -/
theorem noAcceptedArithmeticEdge_iff_threeRejections_of_radicalSmall
    (F : NormalForm T P) (R : ℕ)
    (hsmall : T.RadicalSmall P) :
    T.NoAcceptedArithmeticEdge P F.pureSyncGenerators R ↔ F.ThreeRejections R := by
  exact F.noAcceptedArithmeticEdge_iff_threeRejections_of_ports R
    (F.cSurplusPorts_eq_singleton_two_of_radicalSmall hsmall)

/-- Forward form of the Step 9 equivalence. -/
theorem threeRejections_of_noAcceptedArithmeticEdge_of_radicalSmall
    (F : NormalForm T P) (R : ℕ)
    (hsmall : T.RadicalSmall P)
    (hno : T.NoAcceptedArithmeticEdge P F.pureSyncGenerators R) :
    F.ThreeRejections R := by
  exact (F.noAcceptedArithmeticEdge_iff_threeRejections_of_radicalSmall R hsmall).mp hno

/-- Reverse form of the Step 9 equivalence. -/
theorem noAcceptedArithmeticEdge_of_threeRejections_of_radicalSmall
    (F : NormalForm T P) (R : ℕ)
    (hsmall : T.RadicalSmall P)
    (hthree : F.ThreeRejections R) :
    T.NoAcceptedArithmeticEdge P F.pureSyncGenerators R := by
  exact (F.noAcceptedArithmeticEdge_iff_threeRejections_of_radicalSmall R hsmall).mpr hthree

end NormalForm
end CollisionFrontierPureTwo2
end ABCData
end ABD3
