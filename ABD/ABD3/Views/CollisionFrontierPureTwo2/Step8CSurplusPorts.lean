--import Mathlib.Tactic
import ABD.ABD3.Views.CollisionFrontierPureTwo2.Step7RadicalSmall
import ABD.ABD3.Views.DPlusGraph.LocalSurplus

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo2
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- C-valuation at the pure C-prime `2` is exactly the C-exponent `w`. -/
theorem valC_two_eq_w (F : NormalForm T P) :
    T.valC 2 = F.w := by
  have hfac : vp (2 ^ F.w) 2 = F.w := by
    simpa [vp] using
      (Nat.factorization_pow_self (p := 2) (n := F.w) Nat.prime_two)
  simpa [valC, F.C_eq_two_pow] using hfac

/-- The A-prime contributes no C-valuation in the pure two-power model. -/
theorem valC_p_eq_zero (F : NormalForm T P) :
    T.valC F.p = 0 := by
  have hpnot : F.p ∉ T.supportC := by
    rw [F.supportC_eq_singleton_two]
    simp [F.p_ne_two]
  have hpnot' : F.p ∉ primeSupport T.C.val := by
    simpa [supportC] using hpnot
  have hz : T.C.val.factorization F.p = 0 := by
    exact Finsupp.notMem_support_iff.mp (by
      simpa [primeSupport] using hpnot')
  simpa [valC, vp] using hz

/-- The B-prime contributes no C-valuation in the pure two-power model. -/
theorem valC_q_eq_zero (F : NormalForm T P) :
    T.valC F.q = 0 := by
  have hqnot : F.q ∉ T.supportC := by
    rw [F.supportC_eq_singleton_two]
    simp [F.q_ne_two]
  have hqnot' : F.q ∉ primeSupport T.C.val := by
    simpa [supportC] using hqnot
  have hz : T.C.val.factorization F.q = 0 := by
    exact Finsupp.notMem_support_iff.mp (by
      simpa [primeSupport] using hqnot')
  simpa [valC, vp] using hz

/-- The A-side prime is never a positive C-surplus port. -/
theorem p_not_mem_cSurplusPorts (F : NormalForm T P) :
    F.p ∉ T.CSurplusPorts P := by
  intro hpport
  have hmem := (T.mem_cSurplusPorts_iff P F.p).mp hpport
  have hreward : T.CValuationRewardAt P F.p = 0 := by
    simpa using T.cValuationRewardAt_of_valC_eq_zero P F.valC_p_eq_zero
  have hpos : T.PositiveSurplusExpAt P F.p = 0 := by
    unfold PositiveSurplusExpAt
    rw [hreward]
    simp
  simpa [hpos] using hmem.2

/-- The B-side prime is never a positive C-surplus port. -/
theorem q_not_mem_cSurplusPorts (F : NormalForm T P) :
    F.q ∉ T.CSurplusPorts P := by
  intro hqport
  have hmem := (T.mem_cSurplusPorts_iff P F.q).mp hqport
  have hreward : T.CValuationRewardAt P F.q = 0 := by
    simpa using T.cValuationRewardAt_of_valC_eq_zero P F.valC_q_eq_zero
  have hpos : T.PositiveSurplusExpAt P F.q = 0 := by
    unfold PositiveSurplusExpAt
    rw [hreward]
    simp
  simpa [hpos] using hmem.2

/-- Exponent extraction in the pure two-power model.

From the explicit radical-small inequality
`(2*p*q)^N < (2^w)^M`, positivity of `p` and `q` gives
`2 ≤ 2*p*q`. Hence `2^N ≤ (2*p*q)^N < (2^w)^M = 2^(w*M)`, so
monotonicity of powers of `2` yields `N < M*w`. -/
theorem N_lt_M_mul_w_of_explicitRadicalSmall
    (F : NormalForm T P)
    (hsmall : F.ExplicitRadicalSmall) :
    P.N < P.M * F.w := by
  unfold ExplicitRadicalSmall at hsmall
  have hsmallNat :
      (2 * F.p * F.q) ^ P.N < (2 ^ F.w) ^ P.M := by
    exact_mod_cast hsmall
  have hp1 : 1 ≤ F.p := Nat.succ_le_of_lt F.p_pos
  have hq1 : 1 ≤ F.q := Nat.succ_le_of_lt F.q_pos
  have hpq1 : 1 ≤ F.p * F.q := Nat.mul_le_mul hp1 hq1
  have hbase : (2 : ℕ) ≤ 2 * F.p * F.q := by
    calc
      (2 : ℕ) = 2 * 1 := by simp
      _ ≤ 2 * (F.p * F.q) := Nat.mul_le_mul_left 2 hpq1
      _ = 2 * F.p * F.q := by ac_rfl
  have hpow_le : (2 : ℕ) ^ P.N ≤ (2 * F.p * F.q) ^ P.N := by
    gcongr
  have hpow_lt : (2 : ℕ) ^ P.N < (2 ^ F.w) ^ P.M :=
    lt_of_le_of_lt hpow_le hsmallNat
  have hpow_lt' : (2 : ℕ) ^ P.N < 2 ^ (F.w * P.M) := by
    simpa [pow_mul] using hpow_lt
  have hN : P.N < F.w * P.M := by
    by_contra hnot
    have hle : F.w * P.M ≤ P.N := Nat.le_of_not_gt hnot
    have hpow_ge : (2 : ℕ) ^ (F.w * P.M) ≤ 2 ^ P.N := by
      exact pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hle
    exact (not_lt_of_ge hpow_ge) hpow_lt'
  simpa [Nat.mul_comm] using hN

/-- The explicit radical-small inequality makes the pure C-prime `2` a positive
C-surplus port.  This is the point where the pure exponent extraction is handed
to the general D+ local-surplus lemma. -/
theorem two_mem_cSurplusPorts_of_explicitRadicalSmall
    (F : NormalForm T P)
    (hsmall : F.ExplicitRadicalSmall) :
    2 ∈ T.CSurplusPorts P := by
  have hgt : P.N < P.M * F.w :=
    F.N_lt_M_mul_w_of_explicitRadicalSmall hsmall
  exact T.mem_cSurplusPorts_of_mem_supportABC_of_valC_eq_of_N_lt_M_mul
    P 2 F.w F.two_mem_supportABC F.valC_two_eq_w hgt

/-- Radical-smallness makes the pure C-prime `2` a positive C-surplus port. -/
theorem two_mem_cSurplusPorts_of_radicalSmall
    (F : NormalForm T P)
    (hsmall : T.RadicalSmall P) :
    2 ∈ T.CSurplusPorts P := by
  exact F.two_mem_cSurplusPorts_of_explicitRadicalSmall
    (F.explicitRadicalSmall_of_radicalSmall hsmall)

/-- Once `2` is known to be positive, the already-proved exclusions of `p` and
`q` identify the positive C-surplus ports as exactly `{2}`. -/
theorem cSurplusPorts_eq_singleton_two_of_two_mem
    (F : NormalForm T P)
    (h2 : 2 ∈ T.CSurplusPorts P) :
    T.CSurplusPorts P = {2} := by
  ext x
  constructor
  · intro hx
    have hxmem := (T.mem_cSurplusPorts_iff P x).mp hx
    have hxthree : x ∈ ({2, F.p, F.q} : Support) := by
      simpa [F.supportABC_eq_three] using hxmem.1
    have hx_or : x = 2 ∨ x = F.p ∨ x = F.q := by
      simpa using hxthree
    rcases hx_or with hx2 | hxp | hxq
    · subst x; simp
    · subst x
      exact False.elim (F.p_not_mem_cSurplusPorts hx)
    · subst x
      exact False.elim (F.q_not_mem_cSurplusPorts hx)
  · intro hx
    have hx2 : x = 2 := by
      simpa using hx
    subst x
    exact h2

/-- Main Step 8 output: in the pure two-power model, radical-smallness already
fixes the positive C-surplus ports to the singleton `{2}`. -/
theorem cSurplusPorts_eq_singleton_two_of_radicalSmall
    (F : NormalForm T P)
    (hsmall : T.RadicalSmall P) :
    T.CSurplusPorts P = {2} := by
  exact F.cSurplusPorts_eq_singleton_two_of_two_mem
    (F.two_mem_cSurplusPorts_of_radicalSmall hsmall)

end NormalForm
end CollisionFrontierPureTwo2
end ABCData
end ABD3
