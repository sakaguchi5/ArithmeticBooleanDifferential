import ABD.ABD3.Views.CollisionFrontierPureTwo.Step6CoeffScalesReal

namespace ABD3
namespace ABCData
namespace PureTwoPowerNormalForm

variable {T : ABCData} {P : PowerData}

/-- Real arithmetic lemma behind the Step 6 coefficient-scale factory.

For a prime power `p^e`, the ABD/Pasten coefficient at its own prime direction is

`v_p(p^e) * (p^e / p) = e * p^(e-1)`.

The statement is written with `Int.natAbs` because the graph layer uses natural
coefficient scales. -/
theorem coeffOf_prime_pow_self_natAbs
    {p e : ℕ} (hp : Nat.Prime p) (he : 0 < e) :
    Int.natAbs (coeffOf (p ^ e) p) = e * p ^ (e - 1) := by
  have hfac : vp (p ^ e) p = e := by
    simpa [vp] using
      (Nat.factorization_pow_self (p := p) (n := e) hp)
  have hdiv : p ^ e / p = p ^ (e - 1) := by
    cases e with
    | zero =>
        omega
    | succ k =>
        have hdiv' : p ^ Nat.succ k / p = p ^ k := by
          rw [pow_succ']
          exact Nat.mul_div_cancel_left (p ^ k) hp.pos
        simpa using hdiv'
  calc
    Int.natAbs (coeffOf (p ^ e) p)
        = Int.natAbs ((e : ℤ) * ((p ^ (e - 1) : ℕ) : ℤ)) := by
            simp [coeffOf, hfac, hdiv]
    _ = e * p ^ (e - 1) := by
            rw [Int.natAbs_mul]
            simp

/-- Step 7: the Step 6 prime-power coefficient-scale factory is now realized as
an actual theorem. -/
theorem primePowerCoeffScaleFactory_real :
    PrimePowerCoeffScaleFactory := by
  intro p e hp he
  exact coeffOf_prime_pow_self_natAbs hp he

/-- The pure coefficient-scale facts are now available without any external
factory assumption. -/
theorem pureCoeffScaleFacts_real
    (F : PureTwoPowerNormalForm T P) :
    PureCoeffScaleFacts F := by
  exact F.pureCoeffScaleFacts_of_primePowerCoeffScaleFactory
    primePowerCoeffScaleFactory_real

/-- Proposition form of the realized pure coefficient-scale facts. -/
theorem hasPureCoeffScaleFacts_real
    (F : PureTwoPowerNormalForm T P) :
    F.HasPureCoeffScaleFacts := by
  exact ⟨F.pureCoeffScaleFacts_real⟩

/-- A-side coefficient scale is the pure generator, with no remaining factory
input. -/
theorem coeffAbsA_eq_pureGA_real
    (F : PureTwoPowerNormalForm T P) :
    T.coeffAbsA F.p = F.pureGA := by
  exact F.pureCoeffScaleFacts_real.hA

/-- B-side coefficient scale is the pure generator, with no remaining factory
input. -/
theorem coeffAbsB_eq_pureGB_real
    (F : PureTwoPowerNormalForm T P) :
    T.coeffAbsB F.q = F.pureGB := by
  exact F.pureCoeffScaleFacts_real.hB

/-- C-side two-port coefficient scale is the pure generator, with no remaining
factory input. -/
theorem cPortCoeffNat_two_eq_pureGC_real
    (F : PureTwoPowerNormalForm T P) :
    T.CPortCoeffNat 2 = F.pureGC := by
  exact F.pureCoeffScaleFacts_real.hC

/-- Realized pure-model equivalence between the abstract no-accepted-edge
predicate and the three explicit gcd/lcm rejections. -/
theorem noAcceptedArithmeticEdge_iff_threeRejections_real
    (F : PureTwoPowerNormalForm T P) (R : ℕ)
    (hports : T.CSurplusPorts P = {2}) :
    T.NoAcceptedArithmeticEdge P F.pureSyncGenerators R ↔ F.ThreeRejections R := by
  exact F.noAcceptedArithmeticEdge_iff_threeRejections R hports
    F.cPortCoeffNat_two_eq_pureGC_real

end PureTwoPowerNormalForm

/-- Step 7 frontier wrapper: a pure desynchronized frontier reduces to the
explicit three-rejection frontier with no remaining coefficient-scale factory
assumption. -/
theorem threeRejectionFrontier_of_desyncFrontier_real
    (P : PowerData) (R : ℕ)
    (T : ABCData)
    (hports : T.CSurplusPorts P = {2}) :
    T.PureTwoPowerDesyncFrontier P R →
      T.PureTwoPowerThreeRejectionFrontier P R := by
  exact T.threeRejectionFrontier_of_desyncFrontier_of_primePowerCoeffScaleFactory
    P R PureTwoPowerNormalForm.primePowerCoeffScaleFactory_real hports

end ABCData
end ABD3
