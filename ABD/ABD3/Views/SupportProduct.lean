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

/-- Expansion facts identifying the raw powers with their prime-local support
products.

This used to be an external hypothesis.  It is kept as a named structure only
as a convenient package for the two expansion theorems below. -/
structure PrimeSupportExpansion (T : ABCData) (P : PowerData) : Prop where
  left_expand : (T.SupportTaxProduct P : ℤ) = ((T.radABC : ℤ) ^ P.N)
  right_expand : (T.CRewardProductOnABC P : ℤ) = ((T.C.val : ℤ) ^ P.M)

/-- The C-support is contained in the full ABC support. -/
theorem supportC_subset_supportABC (T : ABCData) :
    T.supportC ⊆ T.supportABC := by
  intro p hp
  simp [supportABC, hp]

/-- Left expansion, in natural-number form:
the full support-tax product is exactly `radABC^N`. -/
theorem supportTaxProduct_eq_radABC_pow_nat
    (T : ABCData) (P : PowerData) :
    T.SupportTaxProduct P = T.radABC ^ P.N := by
  calc
    T.SupportTaxProduct P
        = T.supportABC.prod (fun p => p ^ P.N) := by
          unfold SupportTaxProduct
          apply Finset.prod_congr rfl
          intro p hp
          simp [SupportTaxAt, SupportTax, hp]
    _ = (T.supportABC.prod (fun p => p)) ^ P.N := by
          rw [Finset.prod_pow]
    _ = T.radABC ^ P.N := by
          rfl

/-- The ordinary factorization product of `C` over its support reconstructs `C`. -/
theorem supportC_factorizationProduct_eq_C (T : ABCData) :
    T.supportC.prod (fun p => p ^ T.valC p) = T.C.val := by
  have hC0 : T.C.val ≠ 0 := ne_of_gt T.C.pos
  unfold supportC primeSupport valC vp
  simpa using (Nat.prod_pow_primeFactors_factorization hC0).symm

/-- The reward product over the full ABC support is already the reward product
over the C-support: outside `supportC`, the C-valuation is zero. -/
theorem cRewardProductOnABC_eq_supportCRewardProduct
    (T : ABCData) (P : PowerData) :
    T.CRewardProductOnABC P =
      T.supportC.prod (fun p => p ^ T.CValuationRewardAt P p) := by
  unfold CRewardProductOnABC
  symm
  refine Finset.prod_subset (T.supportC_subset_supportABC) ?_
  intro p _hpABC hpC
  have hpC' : p ∉ T.C.val.factorization.support := by
    simpa [supportC, primeSupport] using hpC
  have hval : T.valC p = 0 := by
    unfold valC vp
    exact Finsupp.notMem_support_iff.mp hpC'
  simp [CValuationRewardAt, hval]

/-- Right expansion, in natural-number form:
the full-support C-reward product is exactly `C^M`. -/
theorem cRewardProductOnABC_eq_C_pow_nat
    (T : ABCData) (P : PowerData) :
    T.CRewardProductOnABC P = T.C.val ^ P.M := by
  calc
    T.CRewardProductOnABC P
        = T.supportC.prod (fun p => p ^ T.CValuationRewardAt P p) := by
          exact T.cRewardProductOnABC_eq_supportCRewardProduct P
    _ = T.supportC.prod (fun p => (p ^ T.valC p) ^ P.M) := by
          apply Finset.prod_congr rfl
          intro p _hp
          rw [CValuationRewardAt, Nat.mul_comm P.M (T.valC p), pow_mul]
    _ = (T.supportC.prod (fun p => p ^ T.valC p)) ^ P.M := by
          rw [Finset.prod_pow]
    _ = T.C.val ^ P.M := by
          rw [T.supportC_factorizationProduct_eq_C]

/-- The prime-support expansion package is now a theorem for every ABD3 triple. -/
theorem primeSupportExpansion (T : ABCData) (P : PowerData) :
    T.PrimeSupportExpansion P := by
  refine ⟨?_, ?_⟩
  · have h := congrArg (fun n : ℕ => (n : ℤ))
      (T.supportTaxProduct_eq_radABC_pow_nat P)
    simpa using h
  · have h := congrArg (fun n : ℕ => (n : ℤ))
      (T.cRewardProductOnABC_eq_C_pow_nat P)
    simpa using h

/-- Theorem A: radical-smallness is equivalent to the prime-local tax/reward
inequality.  The two prime-support expansions are now proved internally. -/
theorem theoremA_radicalSmall_iff_primeLocalTaxReward
    (T : ABCData) (P : PowerData) :
    T.RadicalSmall P ↔ T.PrimeLocalTaxRewardInequality P := by
  have hexp : T.PrimeSupportExpansion P := T.primeSupportExpansion P
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
