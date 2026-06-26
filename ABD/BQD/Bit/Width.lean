import Mathlib.Data.Finset.Basic

namespace ABD
namespace BQD
namespace Bit

/-- The common-width bit universe: positions `0, ..., w-1`.

Named `bitUniverse` rather than `universe` to avoid Lean keyword/name conflicts. -/
def bitUniverse (w : ℕ) : Finset ℕ :=
  Finset.range w

@[simp] theorem mem_bitUniverse {w i : ℕ} :
    i ∈ bitUniverse w ↔ i < w := by
  simp [bitUniverse]

@[simp] theorem bitUniverse_zero :
    bitUniverse 0 = (∅ : Finset ℕ) := by
  ext i
  simp [bitUniverse]

/-- Membership of the successor position in the common-width bit universe. -/
@[simp] theorem succ_mem_bitUniverse {w i : ℕ} :
    i + 1 ∈ bitUniverse w ↔ i + 1 < w := by
  simp [bitUniverse]

end Bit
end BQD
end ABD
