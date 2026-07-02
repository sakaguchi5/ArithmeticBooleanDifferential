import ABD.Note.ExponentCapacity
import ABD.Note.SupportSafetySharp

/-!
# Coprime triple support-scale safety

This file starts the three-integer version of the support-scale obstruction.

The intended arithmetic setting is:

* `1 < a < b < c`;
* `a`, `b`, `c` are pairwise coprime;
* no equation `a + b = c` is needed at this layer.

The core statements are still log-accounting statements.  The pairwise-coprime
condition is recorded as a natural-number predicate, while the actual support
safety is expressed through the total logarithmic radical

`logRad(a) + logRad(b) + logRad(c)`.

The baseline minimal coprime triple skeleton is `{2,3,5}`, whose log-radical
cost is

`log₂ 2 + log₂ 3 + log₂ 5`.

Extra support beyond this baseline is measured by `supportLog S w`.
-/

namespace ABD
namespace Note

/-- Three natural numbers are pairwise coprime. -/
def pairwiseCoprime3 (a b c : ℕ) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c

/--
The ordered coprime triple condition used in this note.

No additive relation such as `a + b = c` is included here.
-/
def orderedPairwiseCoprime3 (a b c : ℕ) : Prop :=
  1 < a ∧ a < b ∧ b < c ∧ pairwiseCoprime3 a b c

/-- Total logarithmic scale of a triple. -/
def tripleScale (LA LB LC : ℝ) : ℝ :=
  LA + LB + LC

/-- Total logarithmic radical of a triple. -/
def tripleLogRad (RA RB RC : ℝ) : ℝ :=
  RA + RB + RC

/--
Triple danger score.

Arithmetic reading:
`LA,LB,LC` are `log₂(a),log₂(b),log₂(c)`;
`RA,RB,RC` are `log₂(rad(a)),log₂(rad(b)),log₂(rad(c))`.
-/
def tripleDanger
    (α LA LB LC RA RB RC : ℝ) : ℝ :=
  danger α (tripleScale LA LB LC) (tripleLogRad RA RB RC)

/-- Natural-number triple danger score. -/
noncomputable def natTripleDanger (α : ℝ) (a b c : ℕ) : ℝ :=
  tripleDanger α
    (natLogScale a) (natLogScale b) (natLogScale c)
    (natLogRad a) (natLogRad b) (natLogRad c)

/-- The log-radical cost of the minimal three-support skeleton `{2,3,5}`. -/
noncomputable def minimalCoprimeTripleLogRad : ℝ :=
  log2 2 + log2 3 + log2 5

/-- The fixed-scale danger of the minimal coprime triple skeleton `{2,3,5}`. -/
noncomputable def minimalCoprimeTripleDanger
    (α LA LB LC : ℝ) : ℝ :=
  danger α (tripleScale LA LB LC) minimalCoprimeTripleLogRad

/-- Unfolding lemma for triple danger. -/
theorem tripleDanger_eq
    (α LA LB LC RA RB RC : ℝ) :
    tripleDanger α LA LB LC RA RB RC
      = danger α (tripleScale LA LB LC) (tripleLogRad RA RB RC) := by
  rfl

/--
Qualitative triple safety.

At fixed triple scale, increasing the total logarithmic radical strictly lowers
the triple danger.
-/
theorem triple_larger_total_logRad_is_safer
    {α LA LB LC oldRad newRad : ℝ}
    (hα : 0 < α)
    (hRad : oldRad < newRad) :
    danger α (tripleScale LA LB LC) newRad
      < danger α (tripleScale LA LB LC) oldRad := by
  exact larger_logRad_is_safer hα hRad

/--
Triple support-safety in component form.

If the total log-radical of the second support profile is larger, then the
second profile is safer at the same three scales.
-/
theorem triple_component_logRad_increase_is_safer
    {α LA LB LC RA₁ RB₁ RC₁ RA₂ RB₂ RC₂ : ℝ}
    (hα : 0 < α)
    (hRad :
      tripleLogRad RA₁ RB₁ RC₁ < tripleLogRad RA₂ RB₂ RC₂) :
    tripleDanger α LA LB LC RA₂ RB₂ RC₂
      < tripleDanger α LA LB LC RA₁ RB₁ RC₁ := by
  unfold tripleDanger
  exact larger_logRad_is_safer hα hRad

/--
Non-strict triple safety from a non-strict total log-radical comparison.
-/
theorem triple_component_logRad_increase_le
    {α LA LB LC RA₁ RB₁ RC₁ RA₂ RB₂ RC₂ : ℝ}
    (hα : 0 ≤ α)
    (hRad :
      tripleLogRad RA₁ RB₁ RC₁ ≤ tripleLogRad RA₂ RB₂ RC₂) :
    tripleDanger α LA LB LC RA₂ RB₂ RC₂
      ≤ tripleDanger α LA LB LC RA₁ RB₁ RC₁ := by
  unfold tripleDanger
  exact danger_le_of_logRad_le hα hRad

/--
Minimal skeleton maximality, log-accounting form.

If a triple's total log-radical is at least the `{2,3,5}` baseline, then at the
same scales it is no more dangerous than the minimal skeleton model.
-/
theorem triple_danger_le_minimal_skeleton_of_min_logRad
    {α LA LB LC RA RB RC : ℝ}
    (hα : 0 ≤ α)
    (hmin : minimalCoprimeTripleLogRad ≤ tripleLogRad RA RB RC) :
    tripleDanger α LA LB LC RA RB RC
      ≤ minimalCoprimeTripleDanger α LA LB LC := by
  unfold tripleDanger minimalCoprimeTripleDanger
  exact danger_le_of_logRad_le hα hmin

/--
Strict version of minimal skeleton maximality.
-/
theorem triple_danger_lt_minimal_skeleton_of_strict_min_logRad
    {α LA LB LC RA RB RC : ℝ}
    (hα : 0 < α)
    (hmin : minimalCoprimeTripleLogRad < tripleLogRad RA RB RC) :
    tripleDanger α LA LB LC RA RB RC
      < minimalCoprimeTripleDanger α LA LB LC := by
  unfold tripleDanger minimalCoprimeTripleDanger
  exact danger_lt_of_logRad_lt hα hmin

/--
Natural-number wrapper for the minimal skeleton comparison.

The arithmetic work of proving `hmin` from actual factorization/support data is
kept separate.  This theorem records how the ordered pairwise-coprime setting
feeds into the already-proved log-accounting comparison once `hmin` is supplied.
-/
theorem natTripleDanger_le_minimal_skeleton_of_min_logRad
    {α : ℝ} {a b c : ℕ}
    (hα : 0 ≤ α)
    (_habc : orderedPairwiseCoprime3 a b c)
    (hmin :
      minimalCoprimeTripleLogRad
        ≤ tripleLogRad (natLogRad a) (natLogRad b) (natLogRad c)) :
    natTripleDanger α a b c
      ≤ minimalCoprimeTripleDanger α
          (natLogScale a) (natLogScale b) (natLogScale c) := by
  unfold natTripleDanger
  exact triple_danger_le_minimal_skeleton_of_min_logRad hα hmin

/--
Exact accounting for extra supports beyond the `{2,3,5}` baseline.
-/
theorem triple_extra_support_eq_minimal_minus_drop
    {ι : Type u}
    (α totalScale : ℝ) (S : Finset ι) (w : ι → ℝ) :
    danger α totalScale
        (minimalCoprimeTripleLogRad + supportLog S w)
      =
    danger α totalScale minimalCoprimeTripleLogRad
      - supportDrop α S w := by
  exact danger_after_adding_support_eq
    α totalScale minimalCoprimeTripleLogRad S w

/--
Extra-support safety beyond `{2,3,5}`, with an arbitrary pointwise lower bound.

This is the three-integer analogue of the one-integer support-safety theorem.
-/
theorem triple_extra_support_le_by_card
    {ι : Type u} {α c totalScale : ℝ} {S : Finset ι} {w : ι → ℝ}
    (hα : 0 ≤ α)
    (hw : ∀ i, i ∈ S → c ≤ w i) :
    danger α totalScale
        (minimalCoprimeTripleLogRad + supportLog S w)
      ≤
    danger α totalScale minimalCoprimeTripleLogRad
      - α * ((S.card : ℝ) * c) := by
  exact danger_after_adding_support_le_by_card
    (S := S) (w := w) hα hw

/--
After the minimal coprime triple skeleton `{2,3,5}`, any genuinely new prime
support is at least `7`.  Therefore the rough extra-support drop is bounded
below by `α * |S| * log₂ 7`.

This theorem assumes the pointwise log-weight condition directly.
-/
theorem triple_extra_support_le_by_card_log2_seven
    {ι : Type u} {α totalScale : ℝ} {S : Finset ι} {w : ι → ℝ}
    (hα : 0 ≤ α)
    (hw : ∀ i, i ∈ S → log2 7 ≤ w i) :
    danger α totalScale
        (minimalCoprimeTripleLogRad + supportLog S w)
      ≤
    danger α totalScale minimalCoprimeTripleLogRad
      - α * ((S.card : ℝ) * log2 7) := by
  exact triple_extra_support_le_by_card
    (S := S) (w := w) hα hw

/-- If a natural support value is at least `7`, its log-weight is at least `log₂ 7`. -/
theorem log2_nat_ge_log2_seven_of_seven_le
    {q : ℕ}
    (hq : 7 ≤ q) :
    log2 7 ≤ log2 (q : ℝ) := by
  exact log2_le_log2_of_pos_of_le
    (by norm_num : (0 : ℝ) < 7)
    (by exact_mod_cast hq)

/--
Natural support version of the rough `log₂ 7` extra-support bound.
-/
theorem triple_extra_nat_supports_le_by_card_log2_seven
    {ι : Type u} {α totalScale : ℝ} {S : Finset ι} {q : ι → ℕ}
    (hα : 0 ≤ α)
    (hq : ∀ i, i ∈ S → 7 ≤ q i) :
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
    (fun i hi => log2_nat_ge_log2_seven_of_seven_le (hq i hi))

/--
Sharp total-lower-bound form for extra supports beyond `{2,3,5}`.

The intended instantiation is a certified lower bound such as
`L = log₂ 7 + log₂ 11 + log₂ 13 + ...`.
-/
theorem triple_extra_support_le_by_total_lower
    {ι : Type u} {α L totalScale : ℝ} {S : Finset ι} {w : ι → ℝ}
    (hα : 0 ≤ α)
    (hL : L ≤ supportLog S w) :
    danger α totalScale
        (minimalCoprimeTripleLogRad + supportLog S w)
      ≤
    danger α totalScale minimalCoprimeTripleLogRad
      - α * L := by
  exact danger_after_adding_support_le_by_total_lower
    (S := S) (w := w) hα hL

/--
Component-scale version of the `log₂ 7` extra-support theorem.
-/
theorem triple_extra_support_component_scale_le_by_card_log2_seven
    {ι : Type u} {α LA LB LC : ℝ} {S : Finset ι} {w : ι → ℝ}
    (hα : 0 ≤ α)
    (hw : ∀ i, i ∈ S → log2 7 ≤ w i) :
    danger α (tripleScale LA LB LC)
        (minimalCoprimeTripleLogRad + supportLog S w)
      ≤
    minimalCoprimeTripleDanger α LA LB LC
      - α * ((S.card : ℝ) * log2 7) := by
  exact triple_extra_support_le_by_card_log2_seven
    (S := S) (w := w) hα hw

end Note
end ABD
