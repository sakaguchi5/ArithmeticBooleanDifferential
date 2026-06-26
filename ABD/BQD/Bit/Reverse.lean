import Mathlib.Data.Nat.Basic
import ABD.BQD.Bit.Width

namespace ABD
namespace BQD
namespace Bit

/-- Fixed-width reversal of a bit position.

Inside `bitUniverse w`, this sends `i` to `w - 1 - i`. -/
def revIndex (w i : ℕ) : ℕ :=
  w - 1 - i

/-- Fixed-width reversal maps the common-width bit universe to itself. -/
theorem revIndex_mem_bitUniverse {w i : ℕ} (hi : i ∈ bitUniverse w) :
    revIndex w i ∈ bitUniverse w := by
  rw [mem_bitUniverse] at hi ⊢
  unfold revIndex
  omega

/-- Fixed-width reversal is involutive on the common-width bit universe. -/
theorem revIndex_involutive_on_bitUniverse {w i : ℕ} (hi : i ∈ bitUniverse w) :
    revIndex w (revIndex w i) = i := by
  rw [mem_bitUniverse] at hi
  unfold revIndex
  omega

/-- The reversal of `0` is `w-1`, whenever `0` belongs to the width universe. -/
theorem revIndex_zero (w : ℕ) :
    revIndex w 0 = w - 1 := by
  simp [revIndex]

/-- The top bit reverses to `0`. -/
theorem revIndex_top {w : ℕ} (hw : 0 < w) :
    revIndex w (w - 1) = 0 := by
  unfold revIndex
  omega

end Bit
end BQD
end ABD
