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

end Bit
end BQD
end ABD
