import ABD.ABD3.Views.ValuationConcentrationPrep

namespace ABD3

namespace ABCData

/-- C-side valuation concentration: some C-prime has C-height reward larger
than one unit of radical tax.

In ordinary notation this says that for some `p | C`,
`N < M * v_p(C)`.  This is the prime-local concentration forced by a
radical-small inequality after both sides are expanded over the same support. -/
def HasCValuationConcentration (T : ABCData) (P : PowerData) : Prop :=
  ∃ p : ℕ, p ∈ T.supportC ∧
    (P.N : ℤ) < (T.CValuationRewardAt P p : ℤ)

/-- The C-side positive-surplus formulation is the same as C-valuation
concentration. -/
theorem hasPositiveCSurplus_iff_hasCValuationConcentration
    (T : ABCData) (P : PowerData) :
    T.HasPositiveCSurplus P ↔ T.HasCValuationConcentration P := by
  exact T.theoremB_positiveCSurplus_iff_highCReward P

/-- Theorem D, product-local form: if the prime-local tax/reward inequality
holds, then some prime in the full ABC support has positive exponent surplus.

This is the non-logarithmic product argument: if every local C-reward exponent
were bounded by its local radical-tax exponent, the whole C-reward product would
be bounded by the support-tax product, contradicting the strict inequality. -/
theorem theoremD_primeLocalTaxReward_forces_positiveFullSurplusPrime
    (T : ABCData) (P : PowerData) :
    T.PrimeLocalTaxRewardInequality P →
      T.HasPositiveFullSurplusPrime P := by
  intro hineq
  by_contra hnone
  have hle : ∀ p ∈ T.supportABC,
      T.CValuationRewardAt P p ≤ T.SupportTaxAt P p := by
    intro p hp
    apply T.reward_le_tax_of_not_positive_surplus P p
    intro hpos
    exact hnone ⟨p, hp, hpos⟩
  have hprodNat :
      T.CRewardProductOnABC P ≤ T.SupportTaxProduct P :=
    T.cRewardProductOnABC_le_supportTaxProduct P hle
  have hprodInt :
      (T.CRewardProductOnABC P : ℤ) ≤
        (T.SupportTaxProduct P : ℤ) := by
    exact_mod_cast hprodNat
  exact not_lt_of_ge hprodInt hineq

/-- Theorem D, C-surplus form: the prime-local tax/reward inequality forces a
positive C-side surplus prime. -/
theorem theoremD_primeLocalTaxReward_forces_positiveCSurplus
    (T : ABCData) (P : PowerData) :
    T.PrimeLocalTaxRewardInequality P →
      T.HasPositiveCSurplus P := by
  intro hineq
  exact T.hasPositiveCSurplus_of_hasPositiveFullSurplusPrime P
    (T.theoremD_primeLocalTaxReward_forces_positiveFullSurplusPrime P hineq)

/-- Theorem D, concentration form: the prime-local tax/reward inequality forces
C-side valuation concentration. -/
theorem theoremD_primeLocalTaxReward_forces_CValuationConcentration
    (T : ABCData) (P : PowerData) :
    T.PrimeLocalTaxRewardInequality P →
      T.HasCValuationConcentration P := by
  intro hineq
  exact (T.hasPositiveCSurplus_iff_hasCValuationConcentration P).mp
    (T.theoremD_primeLocalTaxReward_forces_positiveCSurplus P hineq)

/-- Theorem D from radical-smallness: the raw radical-small inequality forces a
positive C-side surplus prime.  The prime-support expansion is now proved by
`primeSupportExpansion`, so no expansion hypothesis is needed. -/
theorem theoremD_radicalSmall_forces_positiveCSurplus
    (T : ABCData) (P : PowerData) :
    T.RadicalSmall P → T.HasPositiveCSurplus P := by
  intro hsmall
  have hlocal : T.PrimeLocalTaxRewardInequality P :=
    (T.theoremA_radicalSmall_iff_primeLocalTaxReward P).mp hsmall
  exact T.theoremD_primeLocalTaxReward_forces_positiveCSurplus P hlocal

/-- Theorem D, final valuation-concentration statement: a radical-small
primitive positive ABC triple has a C-prime whose reward beats the radical tax. -/
theorem theoremD_radicalSmall_forces_CValuationConcentration
    (T : ABCData) (P : PowerData) :
    T.RadicalSmall P → T.HasCValuationConcentration P := by
  intro hsmall
  exact (T.hasPositiveCSurplus_iff_hasCValuationConcentration P).mp
    (T.theoremD_radicalSmall_forces_positiveCSurplus P hsmall)

end ABCData
end ABD3
