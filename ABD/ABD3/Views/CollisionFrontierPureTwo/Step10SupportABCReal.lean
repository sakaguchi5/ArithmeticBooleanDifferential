import ABD.ABD3.Views.CollisionFrontierPureTwo.Step9RadicalFactsReal

namespace ABD3
namespace ABCData
namespace PureTwoPowerNormalForm

variable {T : ABCData} {P : PowerData}

/-- Local support input for Step 10.

For a prime power `p^e` with `e > 0`, its Boolean prime support is the singleton
`{p}`.  This is the remaining factorization-heavy support fact needed to turn
`A=p^u`, `B=q^v`, and `C=2^w` into the full support identity
`supportABC = {2,p,q}`.

A later step can replace this factory by a theorem about `primeSupport`. -/
def PrimePowerSupportFactory : Prop :=
  ∀ ⦃p e : ℕ⦄, Nat.Prime p → 0 < e →
    primeSupport (p ^ e) = ({p} : Support)

/-- Step 10 block-support facts for the pure two-power normal form. -/
structure PureBlockSupportFacts (F : PureTwoPowerNormalForm T P) where
  hsupportA : T.supportA = ({F.p} : Support)
  hsupportB : T.supportB = ({F.q} : Support)
  hsupportC : T.supportC = ({2} : Support)

/-- Proposition form for Step 10 block-support facts. -/
def HasPureBlockSupportFacts (F : PureTwoPowerNormalForm T P) : Prop :=
  Nonempty (PureBlockSupportFacts F)

/-- The prime-power support factory supplies the three block supports of the pure
model. -/
theorem pureBlockSupportFacts_of_primePowerSupportFactory
    (H : PrimePowerSupportFactory)
    (F : PureTwoPowerNormalForm T P) :
    PureBlockSupportFacts F := by
  refine {
    hsupportA := ?_
    hsupportB := ?_
    hsupportC := ?_
  }
  · have h := H F.p_prime F.u_pos
    simpa [supportA, F.A_eq_p_pow_u] using h
  · have h := H F.q_prime F.v_pos
    simpa [supportB, F.B_eq_q_pow_v] using h
  · have h := H Nat.prime_two F.w_pos
    simpa [supportC, F.C_eq_two_pow] using h

/-- Proposition form: the support factory supplies pure block-support facts. -/
theorem hasPureBlockSupportFacts_of_primePowerSupportFactory
    (H : PrimePowerSupportFactory)
    (F : PureTwoPowerNormalForm T P) :
    F.HasPureBlockSupportFacts := by
  exact ⟨F.pureBlockSupportFacts_of_primePowerSupportFactory H⟩

/-- In the pure model, the A prime is not the C prime `2` once the block supports
are known.  The reason is primitive block disjointness: A and C have disjoint
prime supports. -/
theorem p_ne_two_of_pureBlockSupportFacts
    (F : PureTwoPowerNormalForm T P)
    (H : PureBlockSupportFacts F) :
    F.p ≠ 2 := by
  intro hp2
  rcases T.supportBlocksDisjoint with ⟨_hAB, hAC, _hBC⟩
  have hpA : F.p ∈ T.supportA := by
    rw [H.hsupportA]
    simp
  have h2A : 2 ∈ T.supportA := by
    simpa [hp2] using hpA
  have h2C : 2 ∈ T.supportC := by
    rw [H.hsupportC]
    simp
  have hmem : 2 ∈ T.supportA ∩ T.supportC :=
    Finset.mem_inter.mpr ⟨h2A, h2C⟩
  have hbad : 2 ∈ (∅ : Support) := by
    rw [← hAC]
    exact hmem
  simp at hbad

/-- In the pure model, the B prime is not the C prime `2`. -/
theorem q_ne_two_of_pureBlockSupportFacts
    (F : PureTwoPowerNormalForm T P)
    (H : PureBlockSupportFacts F) :
    F.q ≠ 2 := by
  intro hq2
  rcases T.supportBlocksDisjoint with ⟨_hAB, _hAC, hBC⟩
  have hqB : F.q ∈ T.supportB := by
    rw [H.hsupportB]
    simp
  have h2B : 2 ∈ T.supportB := by
    simpa [hq2] using hqB
  have h2C : 2 ∈ T.supportC := by
    rw [H.hsupportC]
    simp
  have hmem : 2 ∈ T.supportB ∩ T.supportC :=
    Finset.mem_inter.mpr ⟨h2B, h2C⟩
  have hbad : 2 ∈ (∅ : Support) := by
    rw [← hBC]
    exact hmem
  simp at hbad

/-- The two A/B base primes are distinct because the normal form stores `p < q`. -/
theorem p_ne_q_of_order (F : PureTwoPowerNormalForm T P) :
    F.p ≠ F.q := by
  exact ne_of_lt F.p_lt_q

/-- The full ABC support is exactly the three-point support `{2,p,q}` once the
three block supports are known. -/
theorem supportABC_eq_three_of_pureBlockSupportFacts
    (F : PureTwoPowerNormalForm T P)
    (H : PureBlockSupportFacts F) :
    T.supportABC = ({2, F.p, F.q} : Support) := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ ({F.p} : Support) ∪ ({F.q} : Support) ∪ ({2} : Support) := by
      simpa [supportABC, H.hsupportA, H.hsupportB, H.hsupportC] using hx
    have hx_or : x = F.p ∨ x = F.q ∨ x = 2 := by
      simpa using hx'
    rcases hx_or with hxp | hxq | hx2
    · subst x
      simp
    · subst x
      simp
    · subst x
      simp
  · intro hx
    have hx_or : x = 2 ∨ x = F.p ∨ x = F.q := by
      simpa using hx
    have hx_union : x ∈ ({F.p} : Support) ∪ ({F.q} : Support) ∪ ({2} : Support) := by
      rcases hx_or with hx2 | hxp | hxq
      · subst x
        simp
      · subst x
        simp
      · subst x
        simp
    simpa [supportABC, H.hsupportA, H.hsupportB, H.hsupportC] using hx_union

/-- Step 10: block-support facts realize the Step 9 support package. -/
theorem pureSupportABCThreeFacts_of_pureBlockSupportFacts
    (F : PureTwoPowerNormalForm T P)
    (H : PureBlockSupportFacts F) :
    F.PureSupportABCThreeFacts := by
  exact {
    hsupportABC := F.supportABC_eq_three_of_pureBlockSupportFacts H
    hp_ne_two := F.p_ne_two_of_pureBlockSupportFacts H
    hq_ne_two := F.q_ne_two_of_pureBlockSupportFacts H
    hp_ne_q := F.p_ne_q_of_order
  }

/-- Step 10 assembly: the prime-power support factory supplies the full Step 9
support package. -/
theorem pureSupportABCThreeFacts_of_primePowerSupportFactory
    (H : PrimePowerSupportFactory)
    (F : PureTwoPowerNormalForm T P) :
    F.PureSupportABCThreeFacts := by
  exact F.pureSupportABCThreeFacts_of_pureBlockSupportFacts
    (F.pureBlockSupportFacts_of_primePowerSupportFactory H)

/-- Step 10 proposition form. -/
theorem hasPureSupportABCThreeFacts_of_primePowerSupportFactory
    (H : PrimePowerSupportFactory)
    (F : PureTwoPowerNormalForm T P) :
    F.HasPureSupportABCThreeFacts := by
  exact ⟨F.pureSupportABCThreeFacts_of_primePowerSupportFactory H⟩

/-- With the Step 10 support factory, `RadicalSmall` is exactly the explicit pure
inequality `(2*p*q)^N < (2^w)^M`. -/
theorem radicalSmall_iff_explicit_of_primePowerSupportFactory
    (H : PrimePowerSupportFactory)
    (F : PureTwoPowerNormalForm T P) :
    T.RadicalSmall P ↔ F.ExplicitRadicalSmall := by
  exact F.radicalSmall_iff_explicit_of_supportABCThreeFacts
    (F.pureSupportABCThreeFacts_of_primePowerSupportFactory H)

end PureTwoPowerNormalForm

/-- Step 10 closes the Step 9 support-realization goal from the prime-power
support factory. -/
theorem pureSupportABCThreeFactsRealGoal_of_primePowerSupportFactory
    (T : ABCData) (P : PowerData)
    (H : PureTwoPowerNormalForm.PrimePowerSupportFactory) :
    T.PureSupportABCThreeFactsRealGoal P := by
  intro F
  exact F.pureSupportABCThreeFacts_of_primePowerSupportFactory H

/-- Step 10 frontier bridge: with the prime-power support factory, the pure
desynchronized frontier is equivalent to the explicit desynchronized frontier. -/
theorem pureTwoPowerDesyncFrontier_iff_explicit_of_primePowerSupportFactory
    (T : ABCData) (P : PowerData) (R : ℕ)
    (H : PureTwoPowerNormalForm.PrimePowerSupportFactory) :
    T.PureTwoPowerDesyncFrontier P R ↔
      T.PureTwoPowerExplicitDesyncFrontier P R := by
  exact T.pureTwoPowerDesyncFrontier_iff_explicit_of_supportABCThreeFacts P R
    (fun F => F.pureSupportABCThreeFacts_of_primePowerSupportFactory H)

/-- Step 10 frontier bridge for the three-rejection form. -/
theorem pureTwoPowerThreeRejectionFrontier_iff_explicit_of_primePowerSupportFactory
    (T : ABCData) (P : PowerData) (R : ℕ)
    (H : PureTwoPowerNormalForm.PrimePowerSupportFactory) :
    T.PureTwoPowerThreeRejectionFrontier P R ↔
      T.PureTwoPowerExplicitThreeRejectionFrontier P R := by
  exact T.pureTwoPowerThreeRejectionFrontier_iff_explicit_of_supportABCThreeFacts P R
    (fun F => F.pureSupportABCThreeFacts_of_primePowerSupportFactory H)

/-- Combine Steps 7--10: assuming singleton C-surplus and the prime-power support
factory, a pure desynchronized frontier reduces to the explicit inequality plus
the three explicit gcd/lcm rejections. -/
theorem explicitThreeRejectionFrontier_of_desyncFrontier_of_primePowerSupportFactory
    (T : ABCData) (P : PowerData) (R : ℕ)
    (hports : T.CSurplusPorts P = {2})
    (H : PureTwoPowerNormalForm.PrimePowerSupportFactory) :
    T.PureTwoPowerDesyncFrontier P R →
      T.PureTwoPowerExplicitThreeRejectionFrontier P R := by
  intro hfrontier
  exact T.explicitThreeRejectionFrontier_of_desyncFrontier_of_supportABCThreeFacts
    P R hports (fun F => F.pureSupportABCThreeFacts_of_primePowerSupportFactory H)
    hfrontier

/-- A named future goal: realize the prime-power support factory as an actual
`primeSupport (p^e) = {p}` theorem. -/
def PrimePowerSupportFactoryRealGoal : Prop :=
  PureTwoPowerNormalForm.PrimePowerSupportFactory

end ABCData
end ABD3
