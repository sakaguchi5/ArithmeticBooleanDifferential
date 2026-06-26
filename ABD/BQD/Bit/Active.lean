import Mathlib.Data.Nat.Bitwise
import ABD.BQD.Bit.Width

namespace ABD
namespace BQD
namespace Bit

/-- Active bit positions of `n` inside the common-width bit universe `0, ..., w-1`.

This is deliberately called `bitActive`, not `support`, so that the generic
BQD language remains separate from prime-support terminology used elsewhere. -/
def bitActive (w n : ℕ) : Finset ℕ :=
  (bitUniverse w).filter fun i => n.testBit i

/-- Active bit positions lie inside the common-width bit universe. -/
theorem bitActive_subset_bitUniverse (w n : ℕ) :
    bitActive w n ⊆ bitUniverse w := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1

@[simp] theorem mem_bitActive {w n i : ℕ} :
    i ∈ bitActive w n ↔ i < w ∧ n.testBit i := by
  simp [bitActive, bitUniverse]

theorem not_mem_bitActive_of_width_le {w n i : ℕ} (h : w ≤ i) :
    i ∉ bitActive w n := by
  intro hi
  have hiw : i < w := (mem_bitActive.mp hi).1
  exact Nat.not_lt_of_ge h hiw

@[simp] theorem bitActive_zero_width (n : ℕ) :
    bitActive 0 n = ∅ := by
  ext i
  simp [bitActive]

/-- Fixed-width bit complement of `n` inside the common-width bit universe.

This is the bitwise NOT operation restricted to positions `0, ..., w-1`.  It is
kept as a finite set of inactive bit positions rather than as an unbounded
natural-number complement. -/
def bitComplement (w n : ℕ) : Finset ℕ :=
  bitUniverse w \ bitActive w n

/-- Fixed-width bit complements lie inside the common-width bit universe. -/
theorem bitComplement_subset_bitUniverse (w n : ℕ) :
    bitComplement w n ⊆ bitUniverse w := by
  intro i hi
  exact (Finset.mem_sdiff.mp hi).1

@[simp] theorem mem_bitComplement {w n i : ℕ} :
    i ∈ bitComplement w n ↔ i < w ∧ ¬ n.testBit i := by
  simp only [bitComplement, bitUniverse, bitActive, Finset.mem_sdiff, Finset.mem_range,
   Finset.mem_filter,
   not_and,Bool.not_eq_true, and_congr_right_iff, Classical.imp_iff_right_iff]
  intro hi
  exact Or.inl hi

/-- Active and complement positions are disjoint. -/
@[simp] theorem bitActive_inter_bitComplement_eq_empty (w n : ℕ) :
    bitActive w n ∩ bitComplement w n = ∅ := by
  ext i
  simp [bitComplement, bitActive]

/-- Complement and active positions are disjoint. -/
@[simp] theorem bitComplement_inter_bitActive_eq_empty (w n : ℕ) :
    bitComplement w n ∩ bitActive w n = ∅ := by
  ext i
  simp [bitComplement, bitActive]

/-- Active and complement positions split the common-width bit universe. -/
@[simp] theorem bitActive_union_bitComplement_eq_bitUniverse (w n : ℕ) :
    bitActive w n ∪ bitComplement w n = bitUniverse w := by
  ext i
  by_cases hi : i < w
  · by_cases hb : n.testBit i
    · simp [bitComplement, bitActive, bitUniverse, hi, hb]
    · simp [bitComplement, bitActive, bitUniverse, hi, hb]
  · simp [bitComplement, bitActive, bitUniverse, hi]

/-- Complement and active positions split the common-width bit universe. -/
@[simp] theorem bitComplement_union_bitActive_eq_bitUniverse (w n : ℕ) :
    bitComplement w n ∪ bitActive w n = bitUniverse w := by
  rw [Finset.union_comm]
  exact bitActive_union_bitComplement_eq_bitUniverse w n

@[simp] theorem bitComplement_zero_width (n : ℕ) :
    bitComplement 0 n = ∅ := by
  ext i
  simp [bitComplement]

end Bit
end BQD
end ABD
