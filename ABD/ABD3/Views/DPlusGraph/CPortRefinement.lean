import ABD.ABD3.Views.DPlusGraph.Generators

namespace ABD3

namespace ABCData

/-- A positive D+ C-port is genuinely a C-side support prime. -/
theorem mem_supportC_of_mem_cSurplusPorts
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hp : p ∈ T.CSurplusPorts P) :
    p ∈ T.supportC := by
  have hmem := (T.mem_cSurplusPorts_iff P p).mp hp
  rcases hmem with ⟨hpABC, hpos⟩
  have hltNat : T.SupportTaxAt P p < T.CValuationRewardAt P p := by
    exact Nat.lt_of_sub_pos hpos
  have hposExp : 0 < T.ExponentSurplusAt P p := by
    unfold ExponentSurplusAt
    exact sub_pos.mpr (by exact_mod_cast hltNat)
  exact T.mem_supportC_of_positive_full_surplus P hpABC hposExp

/-- Positive C-port membership in C-side valuation language. -/
theorem mem_cSurplusPorts_iff_supportC_and_high_reward
    (T : ABCData) (P : PowerData) (p : ℕ) :
    p ∈ T.CSurplusPorts P ↔
      p ∈ T.supportC ∧ P.N < T.CValuationRewardAt P p := by
  constructor
  · intro hp
    have hmem := (T.mem_cSurplusPorts_iff P p).mp hp
    rcases hmem with ⟨hpABC, hpos⟩
    have hpC : p ∈ T.supportC :=
      T.mem_supportC_of_mem_cSurplusPorts P hp
    have hltTax : T.SupportTaxAt P p < T.CValuationRewardAt P p := by
      exact Nat.lt_of_sub_pos hpos
    have htax : T.SupportTaxAt P p = P.N := by
      simp [hpABC]
    exact ⟨hpC, by simpa [htax] using hltTax⟩
  · rintro ⟨hpC, hlt⟩
    have hpABC : p ∈ T.supportABC := T.supportC_subset_supportABC hpC
    refine (T.mem_cSurplusPorts_iff P p).mpr ⟨hpABC, ?_⟩
    have htax : T.SupportTaxAt P p = P.N := by
      simp [hpABC]
    unfold PositiveSurplusExpAt
    rw [htax]
    exact Nat.sub_pos_of_lt hlt


/-- On a C-port, the graph-side coefficient is exactly `v_p(C) * (C / p)`. -/
theorem cPortCoeffNat_eq_valC_mul_C_div
    (T : ABCData) (p : ℕ) :
    T.CPortCoeffNat p = T.valC p * (T.C.val / p) := by
  simp [CPortCoeffNat, coeffC, coeffOf, valC, vp]
  rfl

/-- The same coefficient normal form, specialized to positive C-surplus ports. -/
theorem cPortCoeffNat_eq_valC_mul_C_div_of_mem_cSurplusPorts
    (T : ABCData) (P : PowerData) {p : ℕ}
    (_hp : p ∈ T.CSurplusPorts P) :
    T.CPortCoeffNat p = T.valC p * (T.C.val / p) := by
  exact T.cPortCoeffNat_eq_valC_mul_C_div p

end ABCData

end ABD3
