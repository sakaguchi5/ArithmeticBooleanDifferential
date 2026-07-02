import ABD.Note.PurePower
import ABD.Note.SupportSafetyNat

/-!
# Exponent capacity and pure-power danger order

This file adds two one-integer principles:

* `smallPrimeExponentCapacity`: under the same size bound `N`, a smaller base
  can realize at least the same exponent as a larger base.
* `purePowerSmallerPrimeMoreDangerous_of_nat`: at fixed logarithmic scale, the
  pure power of the smaller prime/base is strictly more dangerous.

The statements are still independent from the rest of ABD.  They are meant as
one-integer support-scale facts used before passing to ordered coprime triples.
-/

namespace ABD
namespace Note

noncomputable section

/--
If `p ≤ q`, then every exponent fitting under the size bound `N` for base `q`
also fits for base `p`.

Arithmetic reading: smaller bases have at least as much exponent capacity under
the same size ceiling.
-/
theorem smallPrimeExponentCapacity
    {p q N e : ℕ}
    (hpq : p ≤ q)
    (hqN : q ^ e ≤ N) :
    p ^ e ≤ N := by
  have hpqPow : p ^ e ≤ q ^ e := by
    exact Nat.pow_le_pow_left hpq e
  exact le_trans hpqPow hqN

/-- Strict-base version of `smallPrimeExponentCapacity`. -/
theorem smallPrimeExponentCapacity_of_lt
    {p q N e : ℕ}
    (hpq : p < q)
    (hqN : q ^ e ≤ N) :
    p ^ e ≤ N := by
  exact smallPrimeExponentCapacity (Nat.le_of_lt hpq) hqN

/-- A lightweight predicate for saying that exponent `e` fits under `N`. -/
def exponentFits (p N e : ℕ) : Prop :=
  p ^ e ≤ N

/--
Predicate form of exponent-capacity monotonicity.

If `p ≤ q`, then any exponent fitting for `q` also fits for `p`.
-/
theorem exponentFits_of_le_base
    {p q N e : ℕ}
    (hpq : p ≤ q)
    (hfit : exponentFits q N e) :
    exponentFits p N e := by
  exact smallPrimeExponentCapacity hpq hfit

/-- Strict-base predicate form. -/
theorem exponentFits_of_lt_base
    {p q N e : ℕ}
    (hpq : p < q)
    (hfit : exponentFits q N e) :
    exponentFits p N e := by
  exact exponentFits_of_le_base (Nat.le_of_lt hpq) hfit

/-- Strict monotonicity of `log₂` on positive reals. -/
theorem log2_lt_log2_of_pos_of_lt
    {x y : ℝ}
    (hx : 0 < x)
    (hxy : x < y) :
    log2 x < log2 y := by
  unfold log2
  have hlog : Real.log x < Real.log y :=
    Real.log_lt_log hx hxy
  have hden : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  exact div_lt_div_of_pos_right hlog hden

/--
If `1 < p < q`, then `log₂ p < log₂ q`.

The primality of `p,q` is not needed for this analytic comparison; order and
positivity are enough.
-/
theorem log2_nat_lt_log2_nat_of_one_lt_of_lt
    {p q : ℕ}
    (hp : 1 < p)
    (hpq : p < q) :
    log2 (p : ℝ) < log2 (q : ℝ) := by
  have hpPosNat : 0 < p :=
    lt_trans Nat.zero_lt_one hp
  have hpPosReal : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hpPosNat
  have hpqReal : (p : ℝ) < (q : ℝ) := by
    exact_mod_cast hpq
  exact log2_lt_log2_of_pos_of_lt hpPosReal hpqReal

/--
Pure-power smaller-prime/base danger theorem.

At fixed scale, if `1 < p < q`, then the pure-power model using `p` is strictly
more dangerous than the pure-power model using `q`.

Arithmetic reading: under the same log-size, the smaller radical base pays a
smaller radical tax, hence has larger danger.
-/
theorem purePowerSmallerPrimeMoreDangerous_of_nat
    {α scale : ℝ} {p q : ℕ}
    (hα : 0 < α)
    (hp : 1 < p)
    (hpq : p < q) :
    purePowerDanger α scale (log2 (q : ℝ))
      < purePowerDanger α scale (log2 (p : ℝ)) := by
  exact pure_power_danger_strict_anti_mono_prime_log
    hα
    (log2_nat_lt_log2_nat_of_one_lt_of_lt hp hpq)

/-- Non-strict version of the pure-power smaller-base comparison. -/
theorem purePowerSmallerPrimeAtLeastAsDangerous_of_nat
    {α scale : ℝ} {p q : ℕ}
    (hα : 0 ≤ α)
    (hp : 1 < p)
    (hpq : p ≤ q) :
    purePowerDanger α scale (log2 (q : ℝ))
      ≤ purePowerDanger α scale (log2 (p : ℝ)) := by
  have hpPosNat : 0 < p :=
    lt_trans Nat.zero_lt_one hp
  have hpPosReal : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hpPosNat
  have hpqReal : (p : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hpq
  have hlog : log2 (p : ℝ) ≤ log2 (q : ℝ) :=
    log2_le_log2_of_pos_of_le hpPosReal hpqReal
  exact pure_power_danger_anti_mono_prime_log hα hlog

end

end Note
end ABD
