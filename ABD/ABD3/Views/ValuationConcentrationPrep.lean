import ABD.ABD3.Views.SurplusNormalForm

namespace ABD3

namespace PowerData

/-- Since `M < N`, the radical exponent denominator `N` is positive. -/
theorem N_pos (P : PowerData) : 0 < P.N := by
  exact lt_of_le_of_lt (Nat.zero_le P.M) P.exponent_lt_one

end PowerData

namespace ABCData

/-- Membership in the C-support is exactly nonzero C-valuation. -/
theorem mem_supportC_iff_valC_ne_zero
    (T : ABCData) (p : ℕ) :
    p ∈ T.supportC ↔ T.valC p ≠ 0 := by
  unfold supportC primeSupport valC vp
  exact Finsupp.mem_support_iff

/-- Outside the C-support, the C-valuation is zero. -/
theorem valC_eq_zero_of_not_mem_supportC
    (T : ABCData) {p : ℕ}
    (hp : p ∉ T.supportC) :
    T.valC p = 0 := by
  by_contra hval
  exact hp ((T.mem_supportC_iff_valC_ne_zero p).mpr hval)

/-- A positive full-support surplus is exactly strict local tax/reward dominance. -/
theorem positive_surplus_iff_tax_lt_reward
    (T : ABCData) (P : PowerData) (p : ℕ) :
    0 < T.ExponentSurplusAt P p ↔
      (T.SupportTaxAt P p : ℤ) < (T.CValuationRewardAt P p : ℤ) := by
  simp [ExponentSurplusAt]

/-- If the reward is bounded by the tax, the local surplus cannot be positive. -/
theorem not_positive_surplus_of_reward_le_tax
    (T : ABCData) (P : PowerData) (p : ℕ)
    (h : T.CValuationRewardAt P p ≤ T.SupportTaxAt P p) :
    ¬ 0 < T.ExponentSurplusAt P p := by
  intro hpos
  have hlt : (T.SupportTaxAt P p : ℤ) <
      (T.CValuationRewardAt P p : ℤ) :=
    (T.positive_surplus_iff_tax_lt_reward P p).mp hpos
  have hle : (T.CValuationRewardAt P p : ℤ) ≤
      (T.SupportTaxAt P p : ℤ) := by
    exact_mod_cast h
  exact not_lt_of_ge hle hlt

/-- If the local surplus is not positive, then the reward is bounded by the tax. -/
theorem reward_le_tax_of_not_positive_surplus
    (T : ABCData) (P : PowerData) (p : ℕ)
    (h : ¬ 0 < T.ExponentSurplusAt P p) :
    T.CValuationRewardAt P p ≤ T.SupportTaxAt P p := by
  by_contra hle
  have hltNat : T.SupportTaxAt P p < T.CValuationRewardAt P p :=
    Nat.lt_of_not_ge hle
  have hlt : (T.SupportTaxAt P p : ℤ) <
      (T.CValuationRewardAt P p : ℤ) := by
    exact_mod_cast hltNat
  exact h ((T.positive_surplus_iff_tax_lt_reward P p).mpr hlt)

/-- A prime outside the C-support has no positive full-support surplus. -/
theorem not_positive_surplus_of_not_mem_supportC
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hp : p ∉ T.supportC) :
    ¬ 0 < T.ExponentSurplusAt P p := by
  apply T.not_positive_surplus_of_reward_le_tax P p
  have hval : T.valC p = 0 := T.valC_eq_zero_of_not_mem_supportC hp
  rw [T.cValuationRewardAt_of_valC_eq_zero P hval]
  exact Nat.zero_le _

/-- If a full-support surplus prime is positive, then it must lie on the C-side. -/
theorem mem_supportC_of_positive_full_surplus
    (T : ABCData) (P : PowerData) {p : ℕ}
    (_hpABC : p ∈ T.supportABC)
    (hpos : 0 < T.ExponentSurplusAt P p) :
    p ∈ T.supportC := by
  by_contra hpC
  exact (T.not_positive_surplus_of_not_mem_supportC P hpC) hpos

/-- Existence of a positive full-support surplus prime.  This is the first
existence target extracted from the prime-local tax/reward inequality. -/
def HasPositiveFullSurplusPrime (T : ABCData) (P : PowerData) : Prop :=
  ∃ p : ℕ, p ∈ T.supportABC ∧ 0 < T.ExponentSurplusAt P p

/-- A positive full-support surplus prime produces a positive C-surplus prime. -/
theorem hasPositiveCSurplus_of_hasPositiveFullSurplusPrime
    (T : ABCData) (P : PowerData) :
    T.HasPositiveFullSurplusPrime P → T.HasPositiveCSurplus P := by
  rintro ⟨p, hpABC, hpos⟩
  have hpC : p ∈ T.supportC :=
    T.mem_supportC_of_positive_full_surplus P hpABC hpos
  refine ⟨p, hpC, ?_⟩
  rwa [T.exponentSurplusAt_eq_cSurplusAt_of_mem_supportC P hpC] at hpos

/-- A support direction is nonzero. -/
theorem ne_zero_of_mem_primeSupport_pos
    {n p : ℕ} (hn : 0 < n)
    (hp : p ∈ primeSupport n) :
    p ≠ 0 := by
  intro hp0
  have hdiv : p ∣ n := dvd_of_mem_primeSupport hp
  rcases hdiv with ⟨k, hk⟩
  rw [hp0, Nat.zero_mul] at hk
  exact (Nat.ne_of_gt hn) hk

/-- A full ABC-support direction is nonzero. -/
theorem ne_zero_of_mem_supportABC
    (T : ABCData) {p : ℕ}
    (hp : p ∈ T.supportABC) :
    p ≠ 0 := by
  rw [supportABC] at hp
  rcases Finset.mem_union.mp hp with hAB | hC
  · rcases Finset.mem_union.mp hAB with hA | hB
    · exact ne_zero_of_mem_primeSupport_pos T.A.pos (by simpa [supportA] using hA)
    · exact ne_zero_of_mem_primeSupport_pos T.B.pos (by simpa [supportB] using hB)
  · exact ne_zero_of_mem_primeSupport_pos T.C.pos (by simpa [supportC] using hC)

/-- A full ABC-support direction is at least one. -/
theorem one_le_of_mem_supportABC
    (T : ABCData) {p : ℕ}
    (hp : p ∈ T.supportABC) :
    1 ≤ p := by
  exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (T.ne_zero_of_mem_supportABC hp))

/-- Local monotonicity of prime powers with respect to the exponent. -/
theorem pow_le_pow_of_le_exponent_on_supportABC
    (T : ABCData) {p a b : ℕ}
    (hp : p ∈ T.supportABC)
    (h : a ≤ b) :
    p ^ a ≤ p ^ b := by
  exact pow_le_pow_right₀ (T.one_le_of_mem_supportABC hp) h

/-- If every local C-reward exponent is bounded by the local support-tax exponent,
then the C-reward product is bounded by the support-tax product.

This is the main product-monotonicity helper needed before Theorem D. -/
theorem cRewardProductOnABC_le_supportTaxProduct
    (T : ABCData) (P : PowerData)
    (h : ∀ p ∈ T.supportABC,
      T.CValuationRewardAt P p ≤ T.SupportTaxAt P p) :
    T.CRewardProductOnABC P ≤ T.SupportTaxProduct P := by
  unfold CRewardProductOnABC SupportTaxProduct
  apply Finset.prod_le_prod'
  intro p hp
  exact T.pow_le_pow_of_le_exponent_on_supportABC hp (h p hp)

end ABCData
end ABD3
