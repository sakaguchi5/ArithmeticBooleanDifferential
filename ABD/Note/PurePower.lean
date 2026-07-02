import ABD.Note.SupportSafety
import ABD.Note.SupportSafetyNat

/-!
# Pure powers and mixed supports

This file formalizes two fixed-scale principles:

* D. If `log₂ 2` is the minimal possible radical-log, then the `2`-pure-power
  model is maximally dangerous at the same scale.
* E. A mixed support with maximal prime log `maxLog` and additional support log
  `restLog > 0` is strictly safer than the pure power using only `maxLog`.
-/

namespace ABD
namespace Note

/-- Pure-power danger with prime-log `pLog` at a fixed scale. -/
def purePowerDanger (α scale pLog : ℝ) : ℝ :=
  danger α scale pLog

/--
At fixed scale, larger radical-log means no larger danger.
-/
theorem danger_le_of_logRad_le
    {α scale radSmall radLarge : ℝ}
    (hα : 0 ≤ α)
    (hrad : radSmall ≤ radLarge) :
    danger α scale radLarge ≤ danger α scale radSmall := by
  unfold danger
  have hmul : α * radSmall ≤ α * radLarge :=
    mul_le_mul_of_nonneg_left hrad hα
  linarith

/--
At fixed scale, strictly larger radical-log means strictly smaller danger.
-/
theorem danger_lt_of_logRad_lt
    {α scale radSmall radLarge : ℝ}
    (hα : 0 < α)
    (hrad : radSmall < radLarge) :
    danger α scale radLarge < danger α scale radSmall := by
  exact larger_logRad_is_safer hα hrad

/--
D. Fixed-scale maximal-danger theorem for the `2`-pure-power model.

If every admissible integer has logarithmic radical at least `log₂ 2`, then its
danger is at most the danger of the same-scale `2`-pure-power model.
-/
theorem two_power_is_maximally_dangerous_of_min_logRad
    {α scale logRad : ℝ}
    (hα : 0 ≤ α)
    (hmin : log2 2 ≤ logRad) :
    danger α scale logRad ≤ purePowerDanger α scale (log2 2) := by
  exact danger_le_of_logRad_le hα hmin

/--
Strict version of the `2`-pure-power maximal-danger theorem.
-/
theorem two_power_is_strictly_more_dangerous_of_lt_logRad
    {α scale logRad : ℝ}
    (hα : 0 < α)
    (hmin : log2 2 < logRad) :
    danger α scale logRad < purePowerDanger α scale (log2 2) := by
  exact danger_lt_of_logRad_lt hα hmin

/--
Among pure powers at the same scale, the smaller prime-log is at least as
dangerous.
-/
theorem pure_power_danger_anti_mono_prime_log
    {α scale pLog qLog : ℝ}
    (hα : 0 ≤ α)
    (hpq : pLog ≤ qLog) :
    purePowerDanger α scale qLog ≤ purePowerDanger α scale pLog := by
  exact danger_le_of_logRad_le hα hpq

/--
Strict pure-power comparison.
-/
theorem pure_power_danger_strict_anti_mono_prime_log
    {α scale pLog qLog : ℝ}
    (hα : 0 < α)
    (hpq : pLog < qLog) :
    purePowerDanger α scale qLog < purePowerDanger α scale pLog := by
  exact danger_lt_of_logRad_lt hα hpq

/--
Exact mixed-support accounting relative to the pure power using the maximal
prime-log.

If a mixed support has radical-log `maxLog + restLog`, then it equals the
`maxLog` pure-power danger minus `α * restLog`.
-/
theorem mixed_support_eq_max_pure_minus_rest
    (α scale maxLog restLog : ℝ) :
    danger α scale (maxLog + restLog)
      = purePowerDanger α scale maxLog - α * restLog := by
  simp [purePowerDanger, danger, mul_add, sub_eq_add_neg, add_assoc, add_comm]

/--
E. Mixed support is safer than the pure power built from its maximal prime-log,
provided the remaining support-log is positive.
-/
theorem mixed_support_safer_than_max_prime_pure_power
    {α scale maxLog restLog : ℝ}
    (hα : 0 < α)
    (hrest : 0 < restLog) :
    danger α scale (maxLog + restLog)
      < purePowerDanger α scale maxLog := by
  exact larger_logRad_is_safer hα (lt_add_of_pos_right maxLog hrest)

/--
Non-strict mixed-support comparison.
-/
theorem mixed_support_le_max_prime_pure_power
    {α scale maxLog restLog : ℝ}
    (hα : 0 ≤ α)
    (hrest : 0 ≤ restLog) :
    danger α scale (maxLog + restLog)
      ≤ purePowerDanger α scale maxLog := by
  exact danger_le_of_logRad_le hα (le_add_of_nonneg_right hrest)

end Note
end ABD
