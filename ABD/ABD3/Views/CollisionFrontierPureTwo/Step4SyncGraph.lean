import ABD.ABD3.Views.CollisionFrontierPureTwo.Step3CoeffScales

namespace ABD3
namespace ABCData
namespace PureTwoPowerNormalForm

variable {T : ABCData} {P : PowerData}

/-- In the pure two-power model, no accepted arithmetic edge should unfold into
rejection of exactly the three edges `A-B`, `A-C`, and `B-C`.

This definition is the concrete three-generator desynchronization normal form. -/
def ThreeRejections (F : PureTwoPowerNormalForm T P) (R : ℕ) : Prop :=
  SyncRejectedBy R F.pureGA F.pureGB ∧
    SyncRejectedBy R F.pureGA F.pureGC ∧
      SyncRejectedBy R F.pureGB F.pureGC

/-- No accepted arithmetic edge implies the three explicit rejections, provided
that the unique positive C-port is exactly `2` and the C-port coefficient scale
is the expected pure scale. -/
theorem threeRejections_of_noAcceptedArithmeticEdge
    (F : PureTwoPowerNormalForm T P) (R : ℕ)
    (hports : T.CSurplusPorts P = {2})
    (hCscale : T.CPortCoeffNat 2 = F.pureGC)
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
      simpa [ThreeRejections, pureSyncGenerators, hCscale]
        using hun.2.1
    · have hmem : 2 ∈ T.CSurplusPorts P := by
        rw [hports]
        simp
      have hun : T.CPortUnabsorbedAt P F.pureSyncGenerators R 2 :=
        T.cPortUnabsorbedAt_of_absorptionLow P F.pureSyncGenerators R hno.2 hmem
      simpa [ThreeRejections, pureSyncGenerators, hCscale]
        using hun.2.2

/-- The three explicit rejections imply no accepted arithmetic edge, again under
the pure single-port identification. -/
theorem noAcceptedArithmeticEdge_of_threeRejections
    (F : PureTwoPowerNormalForm T P) (R : ℕ)
    (hports : T.CSurplusPorts P = {2})
    (hCscale : T.CPortCoeffNat 2 = F.pureGC)
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
    · simpa [ThreeRejections, pureSyncGenerators, hCscale]
        using hthree.2.1
    · simpa [ThreeRejections, pureSyncGenerators, hCscale]
        using hthree.2.2

/-- The advertised pure-model equivalence between the abstract ABD3 no-accepted
edge predicate and the three explicit gcd/lcm rejections. -/
theorem noAcceptedArithmeticEdge_iff_threeRejections
    (F : PureTwoPowerNormalForm T P) (R : ℕ)
    (hports : T.CSurplusPorts P = {2})
    (hCscale : T.CPortCoeffNat 2 = F.pureGC) :
    T.NoAcceptedArithmeticEdge P F.pureSyncGenerators R ↔ F.ThreeRejections R := by
  constructor
  · exact F.threeRejections_of_noAcceptedArithmeticEdge R hports hCscale
  · exact F.noAcceptedArithmeticEdge_of_threeRejections R hports hCscale

end PureTwoPowerNormalForm
end ABCData
end ABD3
