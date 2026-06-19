import ABD.ABD2.Regime.Core

namespace ABD2
namespace ABCTriple

/-- Rational exponent data for a power-saving regime.

The intended exponent is `M / N`.  The inequality `M < N` records the
power-saving condition `M / N < 1` while avoiding rational powers in the Lean
statement. -/
structure RationalPowerSavingData where
  M : ℕ
  N : ℕ
  exponent_lt_one : M < N

/-- Stage 3 regime: rational power-saving expressed without rational powers.

`B < c^(M/N)` is represented by the integer inequality `B^N < c^M`, together
with `0 ≤ B`.  The data field `M < N` records that the exponent is below one. -/
def rationalPowerSavingRegime
    (T : ABCTriple) (data : RationalPowerSavingData) : T.PowerSavingRegime :=
{ accepts := fun B =>
    0 ≤ B ∧ B ^ data.N < ((T.c : ℤ) ^ data.M) }

/-- Constructor for the rational power-saving acceptance predicate. -/
theorem rationalPowerSavingRegime_accepts_of_pow_lt
    (T : ABCTriple) (data : RationalPowerSavingData) {B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M)) :
    (T.rationalPowerSavingRegime data).accepts B := by
  exact ⟨hBnonneg, hpow⟩

/-- Accepted bounds in a rational power-saving regime are exactly the packaged
nonnegativity and power inequality. -/
theorem rationalPowerSavingRegime_accepts_iff
    (T : ABCTriple) (data : RationalPowerSavingData) (B : ℤ) :
    (T.rationalPowerSavingRegime data).accepts B ↔
      0 ≤ B ∧ B ^ data.N < ((T.c : ℤ) ^ data.M) := by
  rfl

/-- The stored exponent is genuinely below one. -/
theorem rationalPowerSavingData_exponent_lt_one
    (data : RationalPowerSavingData) :
    data.M < data.N :=
  data.exponent_lt_one

end ABCTriple
end ABD2
