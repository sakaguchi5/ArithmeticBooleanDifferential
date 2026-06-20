import Mathlib.Data.Nat.Factorization.Basic
import ABD.ABD3.Views.TaxSurplus

namespace ABD3

/-- Exponent of `p` in the factorization of `n`. -/
def vp (n p : ℕ) : ℕ :=
  n.factorization p

namespace ABCData

/-- A-side valuation. -/
def valA (T : ABCData) (p : ℕ) : ℕ :=
  vp T.A.val p

/-- B-side valuation. -/
def valB (T : ABCData) (p : ℕ) : ℕ :=
  vp T.B.val p

/-- C-side valuation. -/
def valC (T : ABCData) (p : ℕ) : ℕ :=
  vp T.C.val p

theorem valA_eq (T : ABCData) (p : ℕ) :
    T.valA p = vp T.A.val p := rfl

theorem valB_eq (T : ABCData) (p : ℕ) :
    T.valB p = vp T.B.val p := rfl

theorem valC_eq (T : ABCData) (p : ℕ) :
    T.valC p = vp T.C.val p := rfl

/-- Constant radical-support tax: one support prime pays `N`. -/
def SupportTax (P : PowerData) : ℕ :=
  P.N

@[simp] theorem supportTax_eq (P : PowerData) :
    SupportTax P = P.N := rfl

/-- Prime-local radical tax for the full ABC radical support.

A prime pays `N` exactly when it belongs to the full ABC support.
This is the local tax corresponding to the radical side `radABC^N`.
-/
def SupportTaxAt (T : ABCData) (P : PowerData) (p : ℕ) : ℕ :=
  if p ∈ T.supportABC then SupportTax P else 0

/-- Prime-local C-side support tax.

This is not the full radical tax. It is a C-side bookkeeping tax,
intended to pair with `CValuationRewardAt` and `CSurplusAt`.
-/
def CSupportTaxAt (T : ABCData) (P : PowerData) (p : ℕ) : ℕ :=
  if p ∈ T.supportC then SupportTax P else 0

@[simp] theorem supportTaxAt_of_mem_supportABC
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hp : p ∈ T.supportABC) :
    T.SupportTaxAt P p = P.N := by
  simp [SupportTaxAt, SupportTax, hp]

@[simp] theorem supportTaxAt_of_not_mem_supportABC
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hp : p ∉ T.supportABC) :
    T.SupportTaxAt P p = 0 := by
  simp [SupportTaxAt, hp]

@[simp] theorem cSupportTaxAt_of_mem_supportC
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hp : p ∈ T.supportC) :
    T.CSupportTaxAt P p = P.N := by
  simp [CSupportTaxAt, SupportTax, hp]

@[simp] theorem cSupportTaxAt_of_not_mem_supportC
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hp : p ∉ T.supportC) :
    T.CSupportTaxAt P p = 0 := by
  simp [CSupportTaxAt, hp]

/-- C-side valuation reward at exponent numerator `M`: a C-prime with valuation `e`
contributes `M * e`. -/
def CValuationRewardAt (T : ABCData) (P : PowerData) (p : ℕ) : ℕ :=
  P.M * T.valC p

@[simp] theorem cValuationRewardAt_eq
    (T : ABCData) (P : PowerData) (p : ℕ) :
    T.CValuationRewardAt P p = P.M * T.valC p := rfl

@[simp] theorem cValuationRewardAt_of_valC_eq_zero
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hp : T.valC p = 0) :
    T.CValuationRewardAt P p = 0 := by
  rw [CValuationRewardAt, hp, Nat.mul_zero]

/-- Signed C-side surplus at a prime:
`M * v_p(C)` minus the C-side support tax. -/
def CSurplusAt (T : ABCData) (P : PowerData) (p : ℕ) : ℤ :=
  (T.CValuationRewardAt P p : ℤ) - (T.CSupportTaxAt P p : ℤ)

/-- On C-support primes, the C-side surplus is `M * v_p(C) - N`. -/
@[simp] theorem cSurplusAt_of_mem_supportC
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hp : p ∈ T.supportC) :
    T.CSurplusAt P p =
      (T.CValuationRewardAt P p : ℤ) - (P.N : ℤ) := by
  simp [CSurplusAt, CSupportTaxAt, SupportTax, hp]

/-- Outside the C-support, the C-side support tax vanishes. -/
@[simp] theorem cSurplusAt_of_not_mem_supportC
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hp : p ∉ T.supportC) :
    T.CSurplusAt P p =
      (T.CValuationRewardAt P p : ℤ) := by
  simp [CSurplusAt, CSupportTaxAt, hp]

/-- If the C-valuation is zero and `p` is outside C-support, the C-surplus is zero. -/
@[simp] theorem cSurplusAt_eq_zero_of_valC_eq_zero_of_not_mem_supportC
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hval : T.valC p = 0)
    (hp : p ∉ T.supportC) :
    T.CSurplusAt P p = 0 := by
  simp [CSurplusAt, CSupportTaxAt, CValuationRewardAt, hval, hp]

/-- Pasten/ABD coefficient scale on a number `n` at prime direction `p`. -/
def coeffOf (n p : ℕ) : ℤ :=
  (vp n p : ℤ) * ((n / p : ℕ) : ℤ)

@[simp] theorem coeffOf_eq_zero_of_val_eq_zero
    {n p : ℕ} (h : vp n p = 0) :
    coeffOf n p = 0 := by
  simp [coeffOf, h]

/-- A-side coefficient scale. -/
def coeffA (T : ABCData) (p : ℕ) : ℤ :=
  coeffOf T.A.val p

/-- B-side coefficient scale. -/
def coeffB (T : ABCData) (p : ℕ) : ℤ :=
  coeffOf T.B.val p

/-- C-side coefficient scale. -/
def coeffC (T : ABCData) (p : ℕ) : ℤ :=
  coeffOf T.C.val p

theorem coeffA_eq (T : ABCData) (p : ℕ) :
    T.coeffA p = coeffOf T.A.val p := rfl

theorem coeffB_eq (T : ABCData) (p : ℕ) :
    T.coeffB p = coeffOf T.B.val p := rfl

theorem coeffC_eq (T : ABCData) (p : ℕ) :
    T.coeffC p = coeffOf T.C.val p := rfl

@[simp] theorem coeffA_eq_zero_of_valA_eq_zero
    (T : ABCData) {p : ℕ} (h : T.valA p = 0) :
    T.coeffA p = 0 := by
  calc
    T.coeffA p = (T.valA p : ℤ) * ((T.A.val / p : ℕ) : ℤ) := rfl
    _ = ((0 : ℕ) : ℤ) * ((T.A.val / p : ℕ) : ℤ) := by
      rw [h]
    _ = 0 := by
      simp

@[simp] theorem coeffB_eq_zero_of_valB_eq_zero
    (T : ABCData) {p : ℕ} (h : T.valB p = 0) :
    T.coeffB p = 0 := by
  calc
    T.coeffB p = (T.valB p : ℤ) * ((T.B.val / p : ℕ) : ℤ) := rfl
    _ = ((0 : ℕ) : ℤ) * ((T.B.val / p : ℕ) : ℤ) := by
      rw [h]
    _ = 0 := by
      simp

@[simp] theorem coeffC_eq_zero_of_valC_eq_zero
    (T : ABCData) {p : ℕ} (h : T.valC p = 0) :
    T.coeffC p = 0 := by
  calc
    T.coeffC p = (T.valC p : ℤ) * ((T.C.val / p : ℕ) : ℤ) := rfl
    _ = ((0 : ℕ) : ℤ) * ((T.C.val / p : ℕ) : ℤ) := by
      rw [h]
    _ = 0 := by
      simp

end ABCData
end ABD3
