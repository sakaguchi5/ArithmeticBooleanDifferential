import ABD.Note.CoprimeTripleMinRad

/-!
# Extra support beyond the `{2,3,5}` coprime-triple skeleton

This file addresses the next two planned steps.

2. Any prime support genuinely outside the minimal skeleton `{2,3,5}` is at
   least `7`.

3. Instead of only using the coarse bound `r * log₂ 7`, one can use a sharp
   certified lower-weight sum, such as

   `log₂ 7 + log₂ 11 + log₂ 13 + ...`.

The sharp theorem is stated in a flexible form: provide a lower-bound weight for
 each new support, and the theorem sums those lower bounds.
-/

namespace ABD
namespace Note

/--
A prime outside `{2,3,5}` is at least `7`.
-/
theorem seven_le_of_prime_not_two_three_five
    {q : ℕ}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2)
    (hq3 : q ≠ 3)
    (hq5 : q ≠ 5) :
    7 ≤ q := by
  have h5le : 5 ≤ q :=
    five_le_of_prime_ne_two_ne_three hq hq2 hq3
  have h5lt : 5 < q :=
    lt_of_le_of_ne h5le (Ne.symm hq5)
  have hq6 : q ≠ 6 := by
    intro h
    have : Nat.Prime 6 := by simpa [h] using hq
    exact (by decide : ¬ Nat.Prime 6) this
  omega

/--
Log-weight version: a prime outside `{2,3,5}` has log-weight at least `log₂ 7`.
-/
theorem log2_nat_ge_log2_seven_of_prime_not_two_three_five
    {q : ℕ}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2)
    (hq3 : q ≠ 3)
    (hq5 : q ≠ 5) :
    log2 7 ≤ log2 (q : ℝ) := by
  exact log2_nat_ge_log2_seven_of_seven_le
    (seven_le_of_prime_not_two_three_five hq hq2 hq3 hq5)

/--
Pointwise form for a finite family of extra supports.
-/
theorem extra_prime_supports_ge_seven
    {ι : Type u} {S : Finset ι} {q : ι → ℕ}
    (hprime : ∀ i, i ∈ S → Nat.Prime (q i))
    (h2 : ∀ i, i ∈ S → q i ≠ 2)
    (h3 : ∀ i, i ∈ S → q i ≠ 3)
    (h5 : ∀ i, i ∈ S → q i ≠ 5) :
    ∀ i, i ∈ S → 7 ≤ q i := by
  intro i hi
  exact seven_le_of_prime_not_two_three_five
    (hprime i hi) (h2 i hi) (h3 i hi) (h5 i hi)

/--
Pointwise log-weight form for a finite family of extra supports.
-/
theorem extra_prime_supports_log2_ge_log2_seven
    {ι : Type u} {S : Finset ι} {q : ι → ℕ}
    (hprime : ∀ i, i ∈ S → Nat.Prime (q i))
    (h2 : ∀ i, i ∈ S → q i ≠ 2)
    (h3 : ∀ i, i ∈ S → q i ≠ 3)
    (h5 : ∀ i, i ∈ S → q i ≠ 5) :
    ∀ i, i ∈ S → log2 7 ≤ log2 (q i : ℝ) := by
  intro i hi
  exact log2_nat_ge_log2_seven_of_prime_not_two_three_five
    (hprime i hi) (h2 i hi) (h3 i hi) (h5 i hi)

/--
Coarse triple safety for extra natural prime supports outside `{2,3,5}`.

This removes the earlier direct assumption `7 ≤ q i`.
-/
theorem triple_extra_prime_supports_le_by_card_log2_seven
    {ι : Type u} {α totalScale : ℝ} {S : Finset ι} {q : ι → ℕ}
    (hα : 0 ≤ α)
    (hprime : ∀ i, i ∈ S → Nat.Prime (q i))
    (h2 : ∀ i, i ∈ S → q i ≠ 2)
    (h3 : ∀ i, i ∈ S → q i ≠ 3)
    (h5 : ∀ i, i ∈ S → q i ≠ 5) :
    danger α totalScale
        (minimalCoprimeTripleLogRad
          + supportLog S (fun i => log2 (q i : ℝ)))
      ≤
    danger α totalScale minimalCoprimeTripleLogRad
      - α * ((S.card : ℝ) * log2 7) := by
  exact triple_extra_support_le_by_card_log2_seven
    (S := S)
    (w := fun i => log2 (q i : ℝ))
    hα
    (extra_prime_supports_log2_ge_log2_seven hprime h2 h3 h5)

/--
The support-log sum is monotone under pointwise lower bounds.

This is the core sharp-bound summation lemma.
-/
theorem supportLog_le_supportLog_of_pointwise
    {ι : Type u} {S : Finset ι} {lower w : ι → ℝ}
    (h : ∀ i, i ∈ S → lower i ≤ w i) :
    supportLog S lower ≤ supportLog S w := by
  simpa [supportLog] using Finset.sum_le_sum h

/--
Sharp extra-support bound using arbitrary certified lower weights.

If each new support has log-weight at least `lower i`, then the safety gain is
at least the sum of those lower weights, not merely `|S| * log₂ 7`.
-/
theorem triple_extra_support_le_by_pointwise_lower_weights
    {ι : Type u} {α totalScale : ℝ} {S : Finset ι} {lower w : ι → ℝ}
    (hα : 0 ≤ α)
    (hlower : ∀ i, i ∈ S → lower i ≤ w i) :
    danger α totalScale
        (minimalCoprimeTripleLogRad + supportLog S w)
      ≤
    danger α totalScale minimalCoprimeTripleLogRad
      - α * supportLog S lower := by
  have hL : supportLog S lower ≤ supportLog S w :=
    supportLog_le_supportLog_of_pointwise hlower
  exact triple_extra_support_le_by_total_lower
    (S := S) (w := w) hα hL

/--
Natural support version of the sharp bound.

Typical use:
`lower i = 7, 11, 13, ...` certified for the ordered/distinct extra supports.
-/
theorem triple_extra_nat_supports_le_by_lower_bounds
    {ι : Type u} {α totalScale : ℝ}
    {S : Finset ι} {lower q : ι → ℕ}
    (hα : 0 ≤ α)
    (hlower_pos : ∀ i, i ∈ S → 0 < lower i)
    (hlower : ∀ i, i ∈ S → lower i ≤ q i) :
    danger α totalScale
        (minimalCoprimeTripleLogRad
          + supportLog S (fun i => log2 (q i : ℝ)))
      ≤
    danger α totalScale minimalCoprimeTripleLogRad
      - α * supportLog S (fun i => log2 (lower i : ℝ)) := by
  refine triple_extra_support_le_by_pointwise_lower_weights
    (S := S)
    (lower := fun i => log2 (lower i : ℝ))
    (w := fun i => log2 (q i : ℝ))
    hα
    ?_
  intro i hi
  exact log2_le_log2_of_pos_of_le
    (by exact_mod_cast hlower_pos i hi)
    (by exact_mod_cast hlower i hi)

/--
A convenient exact-sum theorem for three certified extra supports.

If the three extra support primes are bounded below by `7`, `11`, and `13`,
then the sharp safety drop is at least
`α * (log₂ 7 + log₂ 11 + log₂ 13)`.
-/
theorem triple_extra_three_nat_supports_le_by_7_11_13
    {α totalScale : ℝ} {q0 q1 q2 : ℕ}
    (hα : 0 ≤ α)
    (hq0 : 7 ≤ q0)
    (hq1 : 11 ≤ q1)
    (hq2 : 13 ≤ q2) :
    danger α totalScale
        (minimalCoprimeTripleLogRad
          + (log2 (q0 : ℝ) + log2 (q1 : ℝ) + log2 (q2 : ℝ)))
      ≤
    danger α totalScale minimalCoprimeTripleLogRad
      - α * (log2 7 + log2 11 + log2 13) := by
  have h0 : log2 7 ≤ log2 (q0 : ℝ) :=
    log2_le_log2_of_pos_of_le
      (by norm_num : (0 : ℝ) < 7)
      (by exact_mod_cast hq0)
  have h1 : log2 11 ≤ log2 (q1 : ℝ) :=
    log2_le_log2_of_pos_of_le
      (by norm_num : (0 : ℝ) < 11)
      (by exact_mod_cast hq1)
  have h2' : log2 13 ≤ log2 (q2 : ℝ) :=
    log2_le_log2_of_pos_of_le
      (by norm_num : (0 : ℝ) < 13)
      (by exact_mod_cast hq2)
  have hsum :
      log2 7 + log2 11 + log2 13
        ≤ log2 (q0 : ℝ) + log2 (q1 : ℝ) + log2 (q2 : ℝ) := by
    linarith
  have hαmul :
      α * (log2 7 + log2 11 + log2 13)
        ≤ α * (log2 (q0 : ℝ) + log2 (q1 : ℝ) + log2 (q2 : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hsum hα
  have hexact :
      danger α totalScale
        (minimalCoprimeTripleLogRad
          + (log2 (q0 : ℝ) + log2 (q1 : ℝ) + log2 (q2 : ℝ)))
      =
      danger α totalScale minimalCoprimeTripleLogRad
        - α * (log2 (q0 : ℝ) + log2 (q1 : ℝ) + log2 (q2 : ℝ)) := by
    unfold danger
    ring
  rw [hexact]
  exact sub_le_sub_left hαmul (danger α totalScale minimalCoprimeTripleLogRad)

end Note
end ABD
