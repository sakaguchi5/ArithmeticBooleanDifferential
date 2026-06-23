import ABD.ABD3.Views.DPlusGraph.CPort

namespace ABD3
namespace ABCData

/-- Local D+ surplus criterion, stated directly in the language of the
positive-surplus exponent.

This is the smallest reusable bridge from a local tax/reward inequality to the
C-port filter: if a prime belongs to the full ABC support and its C-reward is
strictly larger than its radical tax, then it is a positive C-surplus port. -/
theorem mem_cSurplusPorts_of_supportTax_lt_reward
    (T : ABCData) (P : PowerData) (r : ℕ)
    (hr : r ∈ T.supportABC)
    (hgt : T.SupportTaxAt P r < T.CValuationRewardAt P r) :
    r ∈ T.CSurplusPorts P := by
  rw [T.mem_cSurplusPorts_iff P r]
  refine ⟨hr, ?_⟩
  unfold PositiveSurplusExpAt
  exact Nat.sub_pos_of_lt hgt

/-- Local D+ surplus criterion in the common `N < M*v_r(C)` form.

For a prime already in the full ABC support, its radical tax is `N`; its C-side
reward is `M * v_r(C)`.  Hence `N < M * v_r(C)` puts the prime into
`CSurplusPorts`. -/
theorem mem_cSurplusPorts_of_mem_supportABC_of_N_lt_M_mul_valC
    (T : ABCData) (P : PowerData) (r : ℕ)
    (hr : r ∈ T.supportABC)
    (hgt : P.N < P.M * T.valC r) :
    r ∈ T.CSurplusPorts P := by
  apply T.mem_cSurplusPorts_of_supportTax_lt_reward P r hr
  have htax : T.SupportTaxAt P r = P.N :=
    T.supportTaxAt_of_mem_supportABC P hr
  simpa [CValuationRewardAt, htax] using hgt

/-- Local D+ surplus criterion with the valuation identified externally.

This is convenient in specialized normal forms such as the pure two-power model:
first prove `valC r = w`, then prove `N < M*w`, and this lemma supplies the
membership `r ∈ CSurplusPorts`. -/
theorem mem_cSurplusPorts_of_mem_supportABC_of_valC_eq_of_N_lt_M_mul
    (T : ABCData) (P : PowerData) (r w : ℕ)
    (hr : r ∈ T.supportABC)
    (hval : T.valC r = w)
    (hgt : P.N < P.M * w) :
    r ∈ T.CSurplusPorts P := by
  apply T.mem_cSurplusPorts_of_mem_supportABC_of_N_lt_M_mul_valC P r hr
  simpa [hval] using hgt

end ABCData
end ABD3
