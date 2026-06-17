import Mathlib.Data.Finset.Card
import ABD.Lattice.KernelPointConstruction

namespace ABD

/-- Build an explicit pair of distinct support coordinates from the cardinality
condition `2 ≤ S.card`.

The kernel-point construction itself only needs actual coordinates.  This file
is the bridge from the more mathematical cardinality hypothesis to that
coordinate-pair package.
-/
noncomputable def supportPairOfCardTwo
    (S : Finset ℕ) (hcard : 2 ≤ S.card) : SupportPair S := by
  classical
  have hpos : 0 < S.card :=
    lt_of_lt_of_le (by decide : 0 < 2) hcard
  have hS_nonempty : S.Nonempty :=
    Finset.card_pos.mp hpos
  let a : ℕ := Classical.choose hS_nonempty
  have ha : a ∈ S :=
    Classical.choose_spec hS_nonempty
  have hcard_gt_one : 1 < S.card :=
    Nat.lt_of_succ_le hcard
  have herase_pos : 0 < (S.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    exact Nat.sub_pos_of_lt hcard_gt_one
  have herase_nonempty : (S.erase a).Nonempty :=
    Finset.card_pos.mp herase_pos
  let b : ℕ := Classical.choose herase_nonempty
  have hb_erase : b ∈ S.erase a :=
    Classical.choose_spec herase_nonempty
  have hb_ne_a : b ≠ a :=
    (Finset.mem_erase.mp hb_erase).1
  have hbS : b ∈ S :=
    (Finset.mem_erase.mp hb_erase).2
  exact
    { left := ⟨a, ha⟩
      right := ⟨b, hbS⟩
      ne := by
        intro h
        have hval : a = b := congrArg Subtype.val h
        exact hb_ne_a hval.symm }

/-- Existence form of `supportPairOfCardTwo`. -/
theorem exists_supportPair_of_card_two
    (S : Finset ℕ) (hcard : 2 ≤ S.card) :
    Nonempty (SupportPair S) := by
  exact ⟨supportPairOfCardTwo S hcard⟩

end ABD
