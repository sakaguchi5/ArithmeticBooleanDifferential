import ABD.ABD3.Views.CollisionFrontierPureTwo.Step10SupportABCReal

namespace ABD3
namespace ABCData
namespace PureTwoPowerNormalForm

variable {T : ABCData} {P : PowerData}

/-- A prime divisor of a prime power divides the base prime. -/
theorem prime_dvd_base_of_dvd_prime_pow
    {p q e : ℕ} (hq : Nat.Prime q)
    (hdiv : q ∣ p ^ e) :
    q ∣ p := by
  exact hq.dvd_of_dvd_pow hdiv

/-- A prime divisor of a prime power with prime base is the base prime. -/
theorem prime_eq_base_of_dvd_prime_pow
    {p q e : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hdiv : q ∣ p ^ e) :
    q = p := by
  have hqp_dvd : q ∣ p :=
    prime_dvd_base_of_dvd_prime_pow hq hdiv
  exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp_dvd

/-- Real support computation for a positive prime power.

For a prime `p` and positive exponent `e`, the Boolean prime support of `p^e`
is the singleton `{p}`. -/
theorem primeSupport_prime_pow_self_real
    {p e : ℕ} (hp : Nat.Prime p) (he : 0 < e) :
    primeSupport (p ^ e) = ({p} : Support) := by
  ext q
  constructor
  · intro hqmem
    have hqprime : Nat.Prime q := prime_of_mem_primeSupport hqmem
    have hqdiv : q ∣ p ^ e := dvd_of_mem_primeSupport hqmem
    have hqp : q = p := prime_eq_base_of_dvd_prime_pow hp hqprime hqdiv
    simp [hqp]
  · intro hqmem
    have hqp : q = p := by
      simpa using hqmem
    subst q
    have hfac : (p ^ e).factorization p = e := by
      simpa [vp] using
        (Nat.factorization_pow_self (p := p) (n := e) hp)
    unfold primeSupport
    rw [Finsupp.mem_support_iff]
    rw [hfac]
    exact Nat.ne_of_gt he

/-- Step 11: the Step 10 prime-power support factory is now realized as an actual
theorem. -/
theorem primePowerSupportFactory_real :
    PrimePowerSupportFactory := by
  intro p e hp he
  exact primeSupport_prime_pow_self_real hp he

/-- The pure block-support facts are now available without any external support
factory assumption. -/
theorem pureBlockSupportFacts_real
    (F : PureTwoPowerNormalForm T P) :
    PureBlockSupportFacts F := by
  exact F.pureBlockSupportFacts_of_primePowerSupportFactory
    primePowerSupportFactory_real

/-- Proposition form of the realized pure block-support facts. -/
theorem hasPureBlockSupportFacts_real
    (F : PureTwoPowerNormalForm T P) :
    F.HasPureBlockSupportFacts := by
  exact ⟨F.pureBlockSupportFacts_real⟩

/-- The full support package `{2,p,q}` is now available without any external
support factory assumption. -/
theorem pureSupportABCThreeFacts_real
    (F : PureTwoPowerNormalForm T P) :
    F.PureSupportABCThreeFacts := by
  exact F.pureSupportABCThreeFacts_of_pureBlockSupportFacts
    F.pureBlockSupportFacts_real

/-- Proposition form of the realized full support package. -/
theorem hasPureSupportABCThreeFacts_real
    (F : PureTwoPowerNormalForm T P) :
    F.HasPureSupportABCThreeFacts := by
  exact ⟨F.pureSupportABCThreeFacts_real⟩

/-- The pure radical package is now available without any external support
assumption. -/
theorem pureRadicalFacts_real
    (F : PureTwoPowerNormalForm T P) :
    F.PureRadicalFacts := by
  exact F.pureRadicalFacts_of_supportABCThreeFacts
    F.pureSupportABCThreeFacts_real

/-- Proposition form of the realized radical package. -/
theorem hasPureRadicalFacts_real
    (F : PureTwoPowerNormalForm T P) :
    F.HasPureRadicalFacts := by
  exact ⟨F.pureRadicalFacts_real⟩

/-- Unconditional Step 8 specialization: in the pure two-power model,
`RadicalSmall` is exactly `(2*p*q)^N < (2^w)^M`. -/
theorem radicalSmall_iff_explicit_real
    (F : PureTwoPowerNormalForm T P) :
    T.RadicalSmall P ↔ F.ExplicitRadicalSmall := by
  exact F.radicalSmall_iff_explicit_of_supportABCThreeFacts
    F.pureSupportABCThreeFacts_real

/-- Forward direction of the unconditional radical-small specialization. -/
theorem explicitRadicalSmall_of_radicalSmall_real
    (F : PureTwoPowerNormalForm T P)
    (hsmall : T.RadicalSmall P) :
    F.ExplicitRadicalSmall :=
  (F.radicalSmall_iff_explicit_real).mp hsmall

/-- Reverse direction of the unconditional radical-small specialization. -/
theorem radicalSmall_of_explicitRadicalSmall_real
    (F : PureTwoPowerNormalForm T P)
    (hsmall : F.ExplicitRadicalSmall) :
    T.RadicalSmall P :=
  (F.radicalSmall_iff_explicit_real).mpr hsmall

end PureTwoPowerNormalForm

/-- Step 11 closes the Step 10 prime-power support factory goal. -/
theorem primePowerSupportFactoryRealGoal_real :
    PrimePowerSupportFactoryRealGoal := by
  exact PureTwoPowerNormalForm.primePowerSupportFactory_real

/-- Step 11 closes the Step 9 support-realization goal. -/
theorem pureSupportABCThreeFactsRealGoal_real
    (T : ABCData) (P : PowerData) :
    T.PureSupportABCThreeFactsRealGoal P := by
  exact T.pureSupportABCThreeFactsRealGoal_of_primePowerSupportFactory P
    PureTwoPowerNormalForm.primePowerSupportFactory_real

/-- Step 11 closes the Step 8 radical-facts realization goal. -/
theorem pureRadicalFactsRealGoal_real
    (T : ABCData) (P : PowerData) :
    T.PureRadicalFactsRealGoal P := by
  exact T.pureRadicalFactsRealGoal_of_supportABCThreeFactsRealGoal P
    (T.pureSupportABCThreeFactsRealGoal_real P)

/-- Unconditional frontier-level specialization for the desynchronized pure
frontier. -/
theorem pureTwoPowerDesyncFrontier_iff_explicit_real
    (T : ABCData) (P : PowerData) (R : ℕ) :
    T.PureTwoPowerDesyncFrontier P R ↔
      T.PureTwoPowerExplicitDesyncFrontier P R := by
  exact T.pureTwoPowerDesyncFrontier_iff_explicit_of_primePowerSupportFactory
    P R PureTwoPowerNormalForm.primePowerSupportFactory_real

/-- Unconditional frontier-level specialization for the three-rejection pure
frontier. -/
theorem pureTwoPowerThreeRejectionFrontier_iff_explicit_real
    (T : ABCData) (P : PowerData) (R : ℕ) :
    T.PureTwoPowerThreeRejectionFrontier P R ↔
      T.PureTwoPowerExplicitThreeRejectionFrontier P R := by
  exact T.pureTwoPowerThreeRejectionFrontier_iff_explicit_of_primePowerSupportFactory
    P R PureTwoPowerNormalForm.primePowerSupportFactory_real

/-- Combine Steps 7--11: assuming the positive C-surplus singleton is `{2}`, a
pure desynchronized frontier reduces to the explicit inequality plus the three
explicit gcd/lcm rejections with no remaining coefficient or support factory. -/
theorem explicitThreeRejectionFrontier_of_desyncFrontier_real
    (T : ABCData) (P : PowerData) (R : ℕ)
    (hports : T.CSurplusPorts P = {2}) :
    T.PureTwoPowerDesyncFrontier P R →
      T.PureTwoPowerExplicitThreeRejectionFrontier P R := by
  intro hfrontier
  exact T.explicitThreeRejectionFrontier_of_desyncFrontier_of_primePowerSupportFactory
    P R hports PureTwoPowerNormalForm.primePowerSupportFactory_real hfrontier

end ABCData
end ABD3
