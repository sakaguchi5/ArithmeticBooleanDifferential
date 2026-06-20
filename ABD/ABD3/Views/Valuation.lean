import Mathlib.Data.Nat.Factorization.Basic
import ABD.ABD3.Views.TaxSurplus

namespace ABD3

/-- p-adic exponent using mathlib's factorization map. -/
def val (n p : ℕ) : ℕ :=
  n.factorization p

namespace ABCData

/-- A-side valuation. -/
def valA (T : ABCData) (p : ℕ) : ℕ :=
  val T.A p

/-- B-side valuation. -/
def valB (T : ABCData) (p : ℕ) : ℕ :=
  val T.B p

/-- C-side valuation. -/
def valC (T : ABCData) (p : ℕ) : ℕ :=
  val T.C p

/-- Boolean support tax at exponent denominator `N`: every support prime pays `N`. -/
def SupportTaxAt (_T : ABCData) (P : PowerData) (_p : ℕ) : ℕ :=
  P.N

/-- C-side valuation reward at exponent numerator `M`: a C-prime with valuation `e`
contributes `M * e`. -/
def CValuationRewardAt (T : ABCData) (P : PowerData) (p : ℕ) : ℕ :=
  P.M * T.valC p

/-- Signed C-side surplus at a prime: `M * v_p(C) - N`. -/
def CSurplusAt (T : ABCData) (P : PowerData) (p : ℕ) : ℤ :=
  (T.CValuationRewardAt P p : ℤ) - (T.SupportTaxAt P p : ℤ)

/-- Pasten/ABD coefficient scale on a number `n` at prime direction `p`. -/
def coeffOf (n p : ℕ) : ℤ :=
  (val n p : ℤ) * ((n / p : ℕ) : ℤ)

/-- A-side coefficient scale. -/
def coeffA (T : ABCData) (p : ℕ) : ℤ :=
  coeffOf T.A p

/-- B-side coefficient scale. -/
def coeffB (T : ABCData) (p : ℕ) : ℤ :=
  coeffOf T.B p

/-- C-side coefficient scale. -/
def coeffC (T : ABCData) (p : ℕ) : ℤ :=
  coeffOf T.C p

end ABCData
end ABD3
