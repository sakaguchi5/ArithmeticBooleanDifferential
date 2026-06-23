import ABD.ABD3.Views.CollisionFrontierPureTwo2.Step7RadicalSmall
import ABD.ABD3.Views.DPlusGraph.LocalSurplus

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo2
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- C-valuation at the pure C-prime `2` is `w`. -/
theorem valC_two_eq_w (F : NormalForm T P) :
    T.valC 2 = F.w := by
  have hfac : vp (2 ^ F.w) 2 = F.w := by
    simpa [vp] using
      (Nat.factorization_pow_self (p := 2) (n := F.w) Nat.prime_two)
  simpa [valC, F.C_eq_two_pow] using hfac

/-- The A-prime has zero C-valuation. -/
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

/-- The B-prime has zero C-valuation. -/
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

/-- A-side prime has no positive C-surplus. -/
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

/-- B-side prime has no positive C-surplus. -/
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

/-- The remaining pure two-power numerical extraction.

After moving the C-port membership step to the D+ local lemma, the only
pure-specific hard input is the exponent inequality extracted from
`(2*p*q)^N < (2^w)^M`: namely `N < M*w`. -/
def N_lt_M_mul_w_of_explicitRadicalSmallGoal
    (F : NormalForm T P) : Prop :=
  F.ExplicitRadicalSmall → P.N < P.M * F.w

/-- Hard local input left in the natural hierarchy: radical-smallness forces the
pure C-prime `2` to carry positive C-surplus.

This is kept as the final API used by the frontier layer, but it should be
proved via `N_lt_M_mul_w_of_explicitRadicalSmallGoal` plus the general D+ local
lemma in `DPlusGraph.LocalSurplus`. -/
def TwoMemCSurplusGoal : Prop :=
  T.RadicalSmall P → 2 ∈ T.CSurplusPorts P

/-- Equivalent explicit form of the hard local input. -/
def TwoMemCSurplusExplicitGoal (F : NormalForm T P) : Prop :=
  F.ExplicitRadicalSmall → 2 ∈ T.CSurplusPorts P

/-- Convert the pure-specific exponent extraction `N < M*w` into the explicit
C-surplus membership of `2`, using the general D+ local lemma. -/
theorem twoMemCSurplusExplicitGoal_of_N_lt_M_mul_w_goal
    (F : NormalForm T P)
    (H : F.N_lt_M_mul_w_of_explicitRadicalSmallGoal) :
    F.TwoMemCSurplusExplicitGoal := by
  intro hsmall
  have hgt : P.N < P.M * F.w := H hsmall
  exact T.mem_cSurplusPorts_of_mem_supportABC_of_valC_eq_of_N_lt_M_mul
    P 2 F.w F.two_mem_supportABC F.valC_two_eq_w hgt

/-- Convert the explicit local input to the radical-small local input. -/
theorem twoMemCSurplusGoal_of_explicitGoal
    (F : NormalForm T P)
    (H : F.TwoMemCSurplusExplicitGoal) :
    TwoMemCSurplusGoal (T := T) (P := P) := by
  intro hsmall
  exact H (F.explicitRadicalSmall_of_radicalSmall hsmall)

/-- Convert the pure-specific exponent extraction goal directly into the final
`TwoMemCSurplusGoal` API. -/
theorem twoMemCSurplusGoal_of_N_lt_M_mul_w_goal
    (F : NormalForm T P)
    (H : F.N_lt_M_mul_w_of_explicitRadicalSmallGoal) :
    TwoMemCSurplusGoal (T := T) (P := P) := by
  exact F.twoMemCSurplusGoal_of_explicitGoal
    (F.twoMemCSurplusExplicitGoal_of_N_lt_M_mul_w_goal H)

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

/-- Natural Step 8 statement: under the isolated local input, radical-small pure
models have singleton positive C-surplus port `{2}`. -/
theorem cSurplusPorts_eq_singleton_two_of_radicalSmall
    (F : NormalForm T P)
    (H : TwoMemCSurplusGoal (T := T) (P := P))
    (hsmall : T.RadicalSmall P) :
    T.CSurplusPorts P = {2} := by
  exact F.cSurplusPorts_eq_singleton_two_of_two_mem (H hsmall)

end NormalForm
end CollisionFrontierPureTwo2
end ABCData
end ABD3
