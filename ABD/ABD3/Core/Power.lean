import Mathlib.Data.Nat.Basic

namespace ABD3

/-- Rational power-saving exponent data.

The intended exponent is `M / N`; the field `exponent_lt_one : M < N`
records that this exponent is genuinely below one. -/
structure PowerData where
  M : ℕ
  N : ℕ
  exponent_lt_one : M < N

namespace PowerData

/-- The stored exponent is below one. -/
theorem exponent_lt_one' (P : PowerData) : P.M < P.N :=
  P.exponent_lt_one

end PowerData
end ABD3
