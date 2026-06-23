import ABD.ABD3.Views.CollisionFrontierPureTwo.Step8RadicalSmallExplicit

namespace ABD3
namespace ABCData
namespace PureTwoPowerNormalForm

variable {T : ABCData} {P : PowerData}

/-- Step 9 support-level input for the pure two-power radical computation.

The remaining support reconstruction problem is now concentrated in the single
statement that the full ABC support is exactly `{2, p, q}`.  Together with the
pairwise distinctness of these three prime directions, this is enough to compute
`radABC = 2*p*q`.

Later steps can prove this package from the prime-power normal form
`A = p^u`, `B = q^v`, `C = 2^w` and primitivity. -/
structure PureSupportABCThreeFacts (F : PureTwoPowerNormalForm T P) where
  hsupportABC : T.supportABC = ({2, F.p, F.q} : Support)
  hp_ne_two : F.p ≠ 2
  hq_ne_two : F.q ≠ 2
  hp_ne_q : F.p ≠ F.q

/-- Proposition form for the Step 9 support-level input. -/
def HasPureSupportABCThreeFacts (F : PureTwoPowerNormalForm T P) : Prop :=
  Nonempty (PureSupportABCThreeFacts F)

/-- The radical of the explicit three-point support `{2,p,q}` is `2*p*q`. -/
theorem radABC_eq_two_mul_p_mul_q_of_supportABCThreeFacts
    (F : PureTwoPowerNormalForm T P)
    (H : PureSupportABCThreeFacts F) :
    T.radABC = 2 * F.p * F.q := by
  have h2p : 2 ≠ F.p := H.hp_ne_two.symm
  have h2q : 2 ≠ F.q := H.hq_ne_two.symm
  have hpq : F.p ≠ F.q := H.hp_ne_q
  change radOfSupport T.supportABC = 2 * F.p * F.q
  rw [H.hsupportABC]
  simp [radOfSupport, h2p, h2q, hpq, Nat.mul_assoc]

/-- Step 9: support-level facts realize the Step 8 radical package. -/
theorem pureRadicalFacts_of_supportABCThreeFacts
    (F : PureTwoPowerNormalForm T P)
    (H : PureSupportABCThreeFacts F) :
    F.PureRadicalFacts := by
  exact ⟨F.radABC_eq_two_mul_p_mul_q_of_supportABCThreeFacts H⟩

/-- Proposition form: support-level facts imply pure radical facts. -/
theorem hasPureRadicalFacts_of_supportABCThreeFacts
    (F : PureTwoPowerNormalForm T P)
    (H : PureSupportABCThreeFacts F) :
    F.HasPureRadicalFacts := by
  exact ⟨F.pureRadicalFacts_of_supportABCThreeFacts H⟩

/-- Step 9 core theorem: under the explicit support `{2,p,q}` facts,
`RadicalSmall` is exactly `(2*p*q)^N < (2^w)^M`.

This removes the Step 8 `PureRadicalFacts` package from user-facing applications
and replaces it by a concrete support computation package. -/
theorem radicalSmall_iff_explicit_of_supportABCThreeFacts
    (F : PureTwoPowerNormalForm T P)
    (H : PureSupportABCThreeFacts F) :
    T.RadicalSmall P ↔ F.ExplicitRadicalSmall := by
  exact F.radicalSmall_iff_explicit_of_radicalFacts
    (F.pureRadicalFacts_of_supportABCThreeFacts H)

/-- Forward direction of the Step 9 radical-small specialization. -/
theorem explicitRadicalSmall_of_radicalSmall_of_supportABCThreeFacts
    (F : PureTwoPowerNormalForm T P)
    (H : PureSupportABCThreeFacts F)
    (hsmall : T.RadicalSmall P) :
    F.ExplicitRadicalSmall :=
  (F.radicalSmall_iff_explicit_of_supportABCThreeFacts H).mp hsmall

/-- Reverse direction of the Step 9 radical-small specialization. -/
theorem radicalSmall_of_explicitRadicalSmall_of_supportABCThreeFacts
    (F : PureTwoPowerNormalForm T P)
    (H : PureSupportABCThreeFacts F)
    (hsmall : F.ExplicitRadicalSmall) :
    T.RadicalSmall P :=
  (F.radicalSmall_iff_explicit_of_supportABCThreeFacts H).mpr hsmall

end PureTwoPowerNormalForm

/-- Step 9 support-level realization goal: prove the support package for every
pure two-power normal form.  This is the remaining bridge from
`A=p^u, B=q^v, C=2^w` to `supportABC={2,p,q}`. -/
def PureSupportABCThreeFactsRealGoal (T : ABCData) (P : PowerData) : Prop :=
  ∀ F : PureTwoPowerNormalForm T P, F.PureSupportABCThreeFacts

/-- Step 9 closes the Step 8 radical-facts goal from the support-level goal. -/
theorem pureRadicalFactsRealGoal_of_supportABCThreeFactsRealGoal
    (T : ABCData) (P : PowerData)
    (H : T.PureSupportABCThreeFactsRealGoal P) :
    T.PureRadicalFactsRealGoal P := by
  intro F
  exact F.pureRadicalFacts_of_supportABCThreeFacts (H F)

/-- Bidirectional frontier-level specialization using the Step 9 support package. -/
theorem pureTwoPowerDesyncFrontier_iff_explicit_of_supportABCThreeFacts
    (T : ABCData) (P : PowerData) (R : ℕ)
    (H : ∀ F : PureTwoPowerNormalForm T P, F.PureSupportABCThreeFacts) :
    T.PureTwoPowerDesyncFrontier P R ↔
      T.PureTwoPowerExplicitDesyncFrontier P R := by
  exact T.pureTwoPowerDesyncFrontier_iff_explicit_of_radicalFacts P R
    (fun F => F.pureRadicalFacts_of_supportABCThreeFacts (H F))

/-- Bidirectional three-rejection frontier specialization using the Step 9 support package. -/
theorem pureTwoPowerThreeRejectionFrontier_iff_explicit_of_supportABCThreeFacts
    (T : ABCData) (P : PowerData) (R : ℕ)
    (H : ∀ F : PureTwoPowerNormalForm T P, F.PureSupportABCThreeFacts) :
    T.PureTwoPowerThreeRejectionFrontier P R ↔
      T.PureTwoPowerExplicitThreeRejectionFrontier P R := by
  exact T.pureTwoPowerThreeRejectionFrontier_iff_explicit_of_radicalFacts P R
    (fun F => F.pureRadicalFacts_of_supportABCThreeFacts (H F))

/-- Combine Step 7, Step 8, and Step 9: a pure desynchronized frontier reduces to
`(2*p*q)^N < (2^w)^M` plus the three explicit gcd/lcm rejections, assuming the
singleton C-port and the explicit support `{2,p,q}` package. -/
theorem explicitThreeRejectionFrontier_of_desyncFrontier_of_supportABCThreeFacts
    (T : ABCData) (P : PowerData) (R : ℕ)
    (hports : T.CSurplusPorts P = {2})
    (H : ∀ F : PureTwoPowerNormalForm T P, F.PureSupportABCThreeFacts) :
    T.PureTwoPowerDesyncFrontier P R →
      T.PureTwoPowerExplicitThreeRejectionFrontier P R := by
  intro hfrontier
  exact T.explicitThreeRejectionFrontier_of_desyncFrontier_of_radicalFacts
    P R hports (fun F => F.pureRadicalFacts_of_supportABCThreeFacts (H F)) hfrontier

end ABCData
end ABD3
