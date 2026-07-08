/-
  ABD.ApparitionDepth.HigherTermPowerDivisibilityActual

  Step 21S of the Apparition-Depth Decomposition project.

  This file proves the pure natural-number divisibility target isolated in Step
  21Q.  The key inequality is

      r + 1 <= r * k

  whenever `0 < r` and `2 <= k`; therefore

      p^(r+1) | p^(r*k).
-/

import ABD.ApparitionDepth.BinomialHigherTermsActualProof

namespace ApparitionDepth

/-! ## Actual proof of the higher-power divisibility target -/

/-- If `0 < r` and `2 <= k`, then `r + 1 <= r*k`. -/
theorem higherTerm_exponent_le_mul {r k : Nat}
    (hk : 2 ≤ k) (hr : 0 < r) :
    r + 1 ≤ r * k := by
  have hr_one : 1 ≤ r := Nat.succ_le_of_lt hr
  have hle_double : r + 1 ≤ r + r := Nat.add_le_add_left hr_one r
  have hmul : r * 2 ≤ r * k := Nat.mul_le_mul_left r hk
  have hdouble_le : r + r ≤ r * k := by
    simpa [Nat.mul_two] using hmul
  exact le_trans hle_double hdouble_le

/-- Actual proof of the power divisibility target for a single higher term. -/
theorem higherTermPowerDivisibilityTarget_proof (p r k : Nat) :
    HigherTermPowerDivisibilityTarget p r k := by
  intro hk hr
  exact pow_dvd_pow p (higherTerm_exponent_le_mul hk hr)

/-- Actual proof of the higher-power divisibility target for all `k >= 2`. -/
theorem higherTermPowerDivisibilityForAllHigher_proof (p r : Nat) :
    HigherTermPowerDivisibilityForAllHigher p r :=
  fun k => higherTermPowerDivisibilityTarget_proof p r k

/-- Convenience theorem: the concrete divisibility statement, without unfolding the
 named target. -/
theorem pow_succ_dvd_pow_mul_of_two_le_of_pos
    (p r k : Nat) (hk : 2 ≤ k) (hr : 0 < r) :
    p ^ (r + 1) ∣ p ^ (r * k) :=
  higherTermPowerDivisibilityTarget_proof p r k hk hr

end ApparitionDepth
