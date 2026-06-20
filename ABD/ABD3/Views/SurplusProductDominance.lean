import Mathlib.Tactic
import ABD.ABD3.Views.ValuationConcentration

namespace ABD3

namespace ABCData

/-- Positive product exponent at a full ABC-support prime.

This is the positive part of the local signed exponent surplus
`CValuationRewardAt - SupportTaxAt`, kept as a natural exponent so that it can
be used directly in prime-power products. -/
def PositiveSurplusExpAt (T : ABCData) (P : PowerData) (p : ℕ) : ℕ :=
  T.CValuationRewardAt P p - T.SupportTaxAt P p

/-- Negative product exponent at a full ABC-support prime.

This records the deficit of local C-reward against radical tax, again as a
natural exponent.  A/B-only primes automatically contribute here because their
C-valuation reward is zero. -/
def NegativeDeficitExpAt (T : ABCData) (P : PowerData) (p : ℕ) : ℕ :=
  T.SupportTaxAt P p - T.CValuationRewardAt P p

/-- Product of all positive local C-surplus prime powers over the full ABC
support. -/
def PositiveSurplusProduct (T : ABCData) (P : PowerData) : ℕ :=
  T.supportABC.prod (fun p => p ^ T.PositiveSurplusExpAt P p)

/-- Product of all local radical-tax deficits over the full ABC support. -/
def NegativeDeficitProduct (T : ABCData) (P : PowerData) : ℕ :=
  T.supportABC.prod (fun p => p ^ T.NegativeDeficitExpAt P p)

/-- Product-weighted surplus dominance: the positive C-surplus product beats the
negative deficit product. -/
def SurplusProductDominatesDeficit (T : ABCData) (P : PowerData) : Prop :=
  (T.NegativeDeficitProduct P : ℤ) < (T.PositiveSurplusProduct P : ℤ)

/-- Local exponent balance: reward plus deficit equals tax plus surplus.

This is the natural-number form of splitting a signed local surplus into its
positive and negative parts. -/
theorem surplusBalance_exp
    (T : ABCData) (P : PowerData) (p : ℕ) :
    T.CValuationRewardAt P p + T.NegativeDeficitExpAt P p =
      T.SupportTaxAt P p + T.PositiveSurplusExpAt P p := by
  unfold NegativeDeficitExpAt PositiveSurplusExpAt
  omega

/-- Local prime-power balance induced by the local exponent balance. -/
theorem surplusBalance_pow
    (T : ABCData) (P : PowerData) (p : ℕ) :
    p ^ T.CValuationRewardAt P p * p ^ T.NegativeDeficitExpAt P p =
      p ^ T.SupportTaxAt P p * p ^ T.PositiveSurplusExpAt P p := by
  rw [← pow_add, ← pow_add, T.surplusBalance_exp P p]

/-- Product balance over the full ABC support:
C-reward times total deficit equals radical tax times total positive surplus. -/
theorem surplusBalance_prod
    (T : ABCData) (P : PowerData) :
    T.CRewardProductOnABC P * T.NegativeDeficitProduct P =
      T.SupportTaxProduct P * T.PositiveSurplusProduct P := by
  unfold CRewardProductOnABC NegativeDeficitProduct SupportTaxProduct PositiveSurplusProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _hp
  exact T.surplusBalance_pow P p

/-- The support-tax product is positive. -/
theorem supportTax_pos (T : ABCData) (P : PowerData) :
    0 < T.SupportTaxProduct P := by
  unfold SupportTaxProduct
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.pos_of_ne_zero (T.ne_zero_of_mem_supportABC hp)) _

/-- The C-reward product over the ABC support is positive. -/
theorem cReward_pos (T : ABCData) (P : PowerData) :
    0 < T.CRewardProductOnABC P := by
  unfold CRewardProductOnABC
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.pos_of_ne_zero (T.ne_zero_of_mem_supportABC hp)) _

/-- The positive-surplus product is positive. -/
theorem posSurplus_pos (T : ABCData) (P : PowerData) :
    0 < T.PositiveSurplusProduct P := by
  unfold PositiveSurplusProduct
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.pos_of_ne_zero (T.ne_zero_of_mem_supportABC hp)) _

/-- The negative-deficit product is positive. -/
theorem negDeficit_pos (T : ABCData) (P : PowerData) :
    0 < T.NegativeDeficitProduct P := by
  unfold NegativeDeficitProduct
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.pos_of_ne_zero (T.ne_zero_of_mem_supportABC hp)) _

/-- Prime-local tax/reward inequality is equivalent to product-weighted surplus
being larger than product-weighted deficit.

This is the product version of Theorem D+: the raw radical-small product
inequality is not merely an existence statement; it says that the accumulated
positive C-surplus prime powers dominate all accumulated deficits. -/
theorem taxReward_iff_surplusDominance
    (T : ABCData) (P : PowerData) :
    T.PrimeLocalTaxRewardInequality P ↔
      T.SurplusProductDominatesDeficit P := by
  constructor
  · intro hineq
    unfold PrimeLocalTaxRewardInequality at hineq
    unfold SurplusProductDominatesDeficit
    have hbalNat :=
      T.surplusBalance_prod P
    have hbal :
        (T.CRewardProductOnABC P : ℤ) * (T.NegativeDeficitProduct P : ℤ) =
          (T.SupportTaxProduct P : ℤ) * (T.PositiveSurplusProduct P : ℤ) := by
      exact_mod_cast hbalNat
    have htaxPos : (0 : ℤ) < (T.SupportTaxProduct P : ℤ) := by
      exact_mod_cast T.supportTax_pos P
    have hrewardPos : (0 : ℤ) < (T.CRewardProductOnABC P : ℤ) := by
      exact_mod_cast T.cReward_pos P
    have hposPos : (0 : ℤ) < (T.PositiveSurplusProduct P : ℤ) := by
      exact_mod_cast T.posSurplus_pos P
    have hnegPos : (0 : ℤ) < (T.NegativeDeficitProduct P : ℤ) := by
      exact_mod_cast T.negDeficit_pos P
    nlinarith
  · intro hdom
    unfold PrimeLocalTaxRewardInequality
    unfold SurplusProductDominatesDeficit at hdom
    have hbalNat :=
      T.surplusBalance_prod P
    have hbal :
        (T.CRewardProductOnABC P : ℤ) * (T.NegativeDeficitProduct P : ℤ) =
          (T.SupportTaxProduct P : ℤ) * (T.PositiveSurplusProduct P : ℤ) := by
      exact_mod_cast hbalNat
    have htaxPos : (0 : ℤ) < (T.SupportTaxProduct P : ℤ) := by
      exact_mod_cast T.supportTax_pos P
    have hrewardPos : (0 : ℤ) < (T.CRewardProductOnABC P : ℤ) := by
      exact_mod_cast T.cReward_pos P
    have hposPos : (0 : ℤ) < (T.PositiveSurplusProduct P : ℤ) := by
      exact_mod_cast T.posSurplus_pos P
    have hnegPos : (0 : ℤ) < (T.NegativeDeficitProduct P : ℤ) := by
      exact_mod_cast T.negDeficit_pos P
    nlinarith

/-- Theorem D+, radical-small form: radical-smallness is equivalent to
product-weighted C-surplus dominance. -/
theorem theoremDPlus_iff
    (T : ABCData) (P : PowerData) :
    T.RadicalSmall P ↔ T.SurplusProductDominatesDeficit P := by
  rw [T.theoremA_radicalSmall_iff_primeLocalTaxReward P]
  exact T.taxReward_iff_surplusDominance P

/-- Theorem D+, forward direction: a radical-small triple has positive C-surplus
prime powers that dominate the total negative deficit product. -/
theorem theoremDPlus
    (T : ABCData) (P : PowerData) :
    T.RadicalSmall P → T.SurplusProductDominatesDeficit P := by
  exact (T.theoremDPlus_iff P).mp

end ABCData

end ABD3
