import ABD.ABD3.Views.CollisionFrontierPureTwo.Step5Danger

namespace ABD3
namespace ABCData
namespace PureTwoPowerNormalForm

variable {T : ABCData} {P : PowerData}

/-- Local arithmetic input for Step 6.

For a prime power `p^e`, the ABD/Pasten coefficient scale at its own prime is
`e * p^(e-1)`.  This is the only genuinely factorization-heavy arithmetic fact
needed to turn the pure-model generator names `pureGA`, `pureGB`, and `pureGC`
into actual coefficient scales.

The next step can replace this factory by a real theorem about `coeffOf`. -/
def PrimePowerCoeffScaleFactory : Prop :=
  ∀ ⦃p e : ℕ⦄, Nat.Prime p → 0 < e →
    Int.natAbs (coeffOf (p ^ e) p) = e * p ^ (e - 1)

/-- Step 6 assembly: the prime-power coefficient-scale factory supplies the
coefficient-scale facts for any pure two-power normal form. -/
theorem pureCoeffScaleFacts_of_primePowerCoeffScaleFactory
    (H : PrimePowerCoeffScaleFactory)
    (F : PureTwoPowerNormalForm T P) :
    PureCoeffScaleFacts F := by
  refine {
    hA := ?_
    hB := ?_
    hC := ?_
  }
  · have h := H F.p_prime F.u_pos
    simpa [coeffAbsA, coeffA, pureGA, F.A_eq_p_pow_u] using h
  · have h := H F.q_prime F.v_pos
    simpa [coeffAbsB, coeffB, pureGB, F.B_eq_q_pow_v] using h
  · have h := H Nat.prime_two F.w_pos
    simpa [CPortCoeffNat, coeffC, pureGC, F.C_eq_two_pow] using h

/-- Step 6, proposition form. -/
theorem hasPureCoeffScaleFacts_of_primePowerCoeffScaleFactory
    (H : PrimePowerCoeffScaleFactory)
    (F : PureTwoPowerNormalForm T P) :
    F.HasPureCoeffScaleFacts := by
  exact ⟨F.pureCoeffScaleFacts_of_primePowerCoeffScaleFactory H⟩

/-- A-side coefficient scale is the pure generator once the Step 6 factory is
available. -/
theorem coeffAbsA_eq_pureGA_of_primePowerCoeffScaleFactory
    (H : PrimePowerCoeffScaleFactory)
    (F : PureTwoPowerNormalForm T P) :
    T.coeffAbsA F.p = F.pureGA := by
  exact (F.pureCoeffScaleFacts_of_primePowerCoeffScaleFactory H).hA

/-- B-side coefficient scale is the pure generator once the Step 6 factory is
available. -/
theorem coeffAbsB_eq_pureGB_of_primePowerCoeffScaleFactory
    (H : PrimePowerCoeffScaleFactory)
    (F : PureTwoPowerNormalForm T P) :
    T.coeffAbsB F.q = F.pureGB := by
  exact (F.pureCoeffScaleFacts_of_primePowerCoeffScaleFactory H).hB

/-- C-side two-port coefficient scale is the pure generator once the Step 6
factory is available. -/
theorem cPortCoeffNat_two_eq_pureGC_of_primePowerCoeffScaleFactory
    (H : PrimePowerCoeffScaleFactory)
    (F : PureTwoPowerNormalForm T P) :
    T.CPortCoeffNat 2 = F.pureGC := by
  exact (F.pureCoeffScaleFacts_of_primePowerCoeffScaleFactory H).hC

/-- With the Step 6 coefficient-scale factory, the pure-model no-accepted-edge
predicate is exactly the three explicit rejections, with no extra C-scale input. -/
theorem noAcceptedArithmeticEdge_iff_threeRejections_of_primePowerCoeffScaleFactory
    (H : PrimePowerCoeffScaleFactory)
    (F : PureTwoPowerNormalForm T P) (R : ℕ)
    (hports : T.CSurplusPorts P = {2}) :
    T.NoAcceptedArithmeticEdge P F.pureSyncGenerators R ↔ F.ThreeRejections R := by
  exact F.noAcceptedArithmeticEdge_iff_threeRejections R hports
    (F.cPortCoeffNat_two_eq_pureGC_of_primePowerCoeffScaleFactory H)

end PureTwoPowerNormalForm

/-- Step 6 frontier wrapper: once the prime-power coefficient scale factory is
available, a pure desynchronized frontier automatically reduces to the explicit
three-rejection frontier under the singleton C-port identification. -/
theorem threeRejectionFrontier_of_desyncFrontier_of_primePowerCoeffScaleFactory
    (P : PowerData) (R : ℕ)
    (H : PureTwoPowerNormalForm.PrimePowerCoeffScaleFactory)
    (T : ABCData)
    (hports : T.CSurplusPorts P = {2}) :
    T.PureTwoPowerDesyncFrontier P R →
      T.PureTwoPowerThreeRejectionFrontier P R := by
  exact T.threeRejectionFrontier_of_desyncFrontier P R hports
    (fun F => F.cPortCoeffNat_two_eq_pureGC_of_primePowerCoeffScaleFactory H)

end ABCData
end ABD3
