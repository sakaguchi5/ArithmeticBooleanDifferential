import ABD.ABD3.Views.Valuation

namespace ABD3

open Finset

namespace ABCData

/-- The left side of `radABC^N`, written as a prime-local support-tax product.

Each prime in the full ABC support contributes its local radical tax. -/
def SupportTaxProduct (T : ABCData) (P : PowerData) : ℕ :=
  T.supportABC.prod (fun p => p ^ T.SupportTaxAt P p)

/-- The right side of `C^M`, written on the same full ABC support.

A/B-only primes contribute exponent zero through `valC p = 0`; C-primes
contribute the C-height reward `M * v_p(C)`. -/
def CRewardProductOnABC (T : ABCData) (P : PowerData) : ℕ :=
  T.supportABC.prod (fun p => p ^ T.CValuationRewardAt P p)

/-- The prime-local tax/reward form of the radical-small inequality. -/
def PrimeLocalTaxRewardInequality (T : ABCData) (P : PowerData) : Prop :=
  (T.SupportTaxProduct P : ℤ) < (T.CRewardProductOnABC P : ℤ)

/-- Expansion facts required to identify the raw powers with their prime-local
support products.

This isolates the genuinely arithmetic factorization work.  Once these two
expansions are available, radical-smallness is just the same inequality written
in prime-local tax/reward language. -/
structure PrimeSupportExpansion (T : ABCData) (P : PowerData) : Prop where
  left_expand : (T.SupportTaxProduct P : ℤ) = ((T.radABC : ℤ) ^ P.N)
  right_expand : (T.CRewardProductOnABC P : ℤ) = ((T.C : ℤ) ^ P.M)

/-- Theorem A: radical-smallness is equivalent to the prime-local tax/reward
inequality, once the two sides have been expanded over the common support. -/
theorem theoremA_radicalSmall_iff_primeLocalTaxReward
    (T : ABCData) (P : PowerData)
    (hexp : T.PrimeSupportExpansion P) :
    T.RadicalSmall P ↔ T.PrimeLocalTaxRewardInequality P := by
  unfold RadicalSmall RadicalSmallInt PrimeLocalTaxRewardInequality
  rw [← hexp.left_expand, ← hexp.right_expand]

/-- The left local product is definitionally a product over the full support. -/
theorem supportTaxProduct_eq_prod (T : ABCData) (P : PowerData) :
    T.SupportTaxProduct P =
      T.supportABC.prod (fun p => p ^ T.SupportTaxAt P p) := by
  rfl

/-- The right local product is definitionally a product over the same support. -/
theorem cRewardProductOnABC_eq_prod (T : ABCData) (P : PowerData) :
    T.CRewardProductOnABC P =
      T.supportABC.prod (fun p => p ^ T.CValuationRewardAt P p) := by
  rfl

end ABCData
end ABD3
