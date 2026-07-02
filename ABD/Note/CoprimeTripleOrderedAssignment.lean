import ABD.Note.CoprimeTripleExtraSupport

/-!
# Ordered assignment for the `{2,3,5}` minimal skeleton

This file records the fourth planned piece:

* after the unordered minimal support skeleton `{2,3,5}` has been isolated,
* and the triple is viewed through ordered size slots `A ≤ B ≤ C`,
* the canonical high-power representative places the larger base in the smaller
  slot and the smaller base in the larger slot:

`A : 5`, `B : 3`, `C : 2`.

The results here are intentionally stated as capacity and fixed-scale danger
lemmas.  They do not claim that the total radical product distinguishes the
permutations of `{2,3,5}`; it does not.  Rather, they formalize the ordered
high-power interpretation:

* smaller bases have larger exponent capacity under larger ceilings;
* at a fixed scale, smaller bases are more dangerous.
-/

namespace ABD
namespace Note

/--
The canonical ordered representative of the minimal coprime triple skeleton.

Arithmetic reading:

`a = 5^x`, `b = 3^y`, `c = 2^z`.
-/
def ordered235PureSkeleton
    (a b c x y z : ℕ) : Prop :=
  a = 5 ^ x ∧ b = 3 ^ y ∧ c = 2 ^ z

/--
If `p ≤ q` and the ceiling also grows from `N` to `M`, then every exponent that
fits for `q` under `N` also fits for `p` under `M`.
-/
theorem orderedExponentCapacity_of_le_base_le_ceiling
    {p q N M e : ℕ}
    (hpq : p ≤ q)
    (hNM : N ≤ M)
    (hfit : exponentFits q N e) :
    exponentFits p M e := by
  unfold exponentFits at *
  exact le_trans (smallPrimeExponentCapacity hpq hfit) hNM

/--
Strict-base version of `orderedExponentCapacity_of_le_base_le_ceiling`.
-/
theorem orderedExponentCapacity_of_lt_base_le_ceiling
    {p q N M e : ℕ}
    (hpq : p < q)
    (hNM : N ≤ M)
    (hfit : exponentFits q N e) :
    exponentFits p M e := by
  exact orderedExponentCapacity_of_le_base_le_ceiling
    (Nat.le_of_lt hpq) hNM hfit

/--
If `5^e` fits under the smaller ceiling `A`, then `3^e` fits under any larger
ceiling `B`.
-/
theorem ordered_5_to_3_exponentCapacity
    {A B e : ℕ}
    (hAB : A ≤ B)
    (hfit : exponentFits 5 A e) :
    exponentFits 3 B e := by
  exact orderedExponentCapacity_of_le_base_le_ceiling
    (p := 3) (q := 5) (N := A) (M := B) (e := e)
    (by norm_num)
    hAB
    hfit

/--
If `3^e` fits under the middle ceiling `B`, then `2^e` fits under any larger
ceiling `C`.
-/
theorem ordered_3_to_2_exponentCapacity
    {B C e : ℕ}
    (hBC : B ≤ C)
    (hfit : exponentFits 3 B e) :
    exponentFits 2 C e := by
  exact orderedExponentCapacity_of_le_base_le_ceiling
    (p := 2) (q := 3) (N := B) (M := C) (e := e)
    (by norm_num)
    hBC
    hfit

/--
If `5^e` fits under the smaller ceiling `A`, then `2^e` fits under any larger
ceiling `C`.
-/
theorem ordered_5_to_2_exponentCapacity
    {A C e : ℕ}
    (hAC : A ≤ C)
    (hfit : exponentFits 5 A e) :
    exponentFits 2 C e := by
  exact orderedExponentCapacity_of_le_base_le_ceiling
    (p := 2) (q := 5) (N := A) (M := C) (e := e)
    (by norm_num)
    hAC
    hfit

/--
Capacity chain for the ordered `{5,3,2}` representative.

If `A ≤ B ≤ C` and exponent `e` fits in the smallest slot using base `5`,
then the same exponent fits in the larger slots using bases `3` and `2`.
-/
theorem ordered235ExponentCapacityChain
    {A B C e : ℕ}
    (hAB : A ≤ B)
    (hBC : B ≤ C)
    (hfit5A : exponentFits 5 A e) :
    exponentFits 3 B e ∧ exponentFits 2 C e := by
  refine ⟨?_, ?_⟩
  · exact ordered_5_to_3_exponentCapacity hAB hfit5A
  · exact ordered_5_to_2_exponentCapacity (le_trans hAB hBC) hfit5A

/--
The second half of the capacity chain.

If `3^e` fits in the middle slot, then `2^e` fits in the largest slot.
-/
theorem ordered32ExponentCapacityChain
    {B C e : ℕ}
    (hBC : B ≤ C)
    (hfit3B : exponentFits 3 B e) :
    exponentFits 2 C e := by
  exact ordered_3_to_2_exponentCapacity hBC hfit3B

/--
For ordered natural numbers `1 < a < b < c`, any exponent fitting in `a` with
base `5` also fits in `b` with base `3` and in `c` with base `2`.
-/
theorem ordered235ExponentCapacityChain_of_orderedTriple
    {a b c e : ℕ}
    (habc : orderedPairwiseCoprime3 a b c)
    (hfit5a : exponentFits 5 a e) :
    exponentFits 3 b e ∧ exponentFits 2 c e := by
  rcases habc with ⟨_ha, hab, hbc, _hcop⟩
  exact ordered235ExponentCapacityChain
    (Nat.le_of_lt hab)
    (Nat.le_of_lt hbc)
    hfit5a

/--
At any fixed scale, among the bases `2,3,5`, the smaller base is more
dangerous in the pure-power model:

`5` is safer than `3`, and `3` is safer than `2`.
-/
theorem purePowerDanger_2_3_5_order_at_fixed_scale
    {α scale : ℝ}
    (hα : 0 < α) :
    purePowerDanger α scale (log2 (5 : ℝ))
        < purePowerDanger α scale (log2 (3 : ℝ))
      ∧
    purePowerDanger α scale (log2 (3 : ℝ))
        < purePowerDanger α scale (log2 (2 : ℝ))
      ∧
    purePowerDanger α scale (log2 (5 : ℝ))
        < purePowerDanger α scale (log2 (2 : ℝ)) := by
  have h35 :
      purePowerDanger α scale (log2 (5 : ℝ))
        < purePowerDanger α scale (log2 (3 : ℝ)) := by
    exact purePowerSmallerPrimeMoreDangerous_of_nat
      (α := α) (scale := scale) (p := 3) (q := 5)
      hα
      (by norm_num)
      (by norm_num)
  have h23 :
      purePowerDanger α scale (log2 (3 : ℝ))
        < purePowerDanger α scale (log2 (2 : ℝ)) := by
    exact purePowerSmallerPrimeMoreDangerous_of_nat
      (α := α) (scale := scale) (p := 2) (q := 3)
      hα
      (by norm_num)
      (by norm_num)
  exact ⟨h35, h23, lt_trans h35 h23⟩

/--
The largest slot receives base `2` in the ordered representative because, at
that fixed scale, base `2` is more dangerous than base `3`.
-/
theorem largest_slot_two_more_dangerous_than_three
    {α LC : ℝ}
    (hα : 0 < α) :
    purePowerDanger α LC (log2 (3 : ℝ))
      < purePowerDanger α LC (log2 (2 : ℝ)) := by
  exact (purePowerDanger_2_3_5_order_at_fixed_scale
    (α := α) (scale := LC) hα).2.1

/--
The largest slot receives base `2` in the ordered representative because, at
that fixed scale, base `2` is more dangerous than base `5`.
-/
theorem largest_slot_two_more_dangerous_than_five
    {α LC : ℝ}
    (hα : 0 < α) :
    purePowerDanger α LC (log2 (5 : ℝ))
      < purePowerDanger α LC (log2 (2 : ℝ)) := by
  exact (purePowerDanger_2_3_5_order_at_fixed_scale
    (α := α) (scale := LC) hα).2.2

/--
The middle slot receives base `3` rather than `5` in the ordered representative
because, at that fixed scale, base `3` is more dangerous than base `5`.
-/
theorem middle_slot_three_more_dangerous_than_five
    {α LB : ℝ}
    (hα : 0 < α) :
    purePowerDanger α LB (log2 (5 : ℝ))
      < purePowerDanger α LB (log2 (3 : ℝ)) := by
  exact (purePowerDanger_2_3_5_order_at_fixed_scale
    (α := α) (scale := LB) hα).1

end Note
end ABD
