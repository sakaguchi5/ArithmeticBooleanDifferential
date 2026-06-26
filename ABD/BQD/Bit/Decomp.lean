import ABD.BQD.Calculus.Core
import ABD.BQD.Bit.Active

namespace ABD
namespace BQD
namespace Bit

/-- Bit-level BQD decomposition of two natural numbers at common width `w`. -/
def decomp (w x y : ℕ) : Decomp ℕ where
  U := bitUniverse w
  L := bitActive w x
  R := bitActive w y
  hL := bitActive_subset_bitUniverse w x
  hR := bitActive_subset_bitUniverse w y

@[simp] theorem decomp_U (w x y : ℕ) :
    (decomp w x y).U = bitUniverse w := rfl

@[simp] theorem decomp_L (w x y : ℕ) :
    (decomp w x y).L = bitActive w x := rfl

@[simp] theorem decomp_R (w x y : ℕ) :
    (decomp w x y).R = bitActive w y := rfl

@[simp] theorem mem_decomp_left {w x y i : ℕ} :
    i ∈ (decomp w x y).L ↔ i < w ∧ x.testBit i := by
  simp [decomp]

@[simp] theorem mem_decomp_right {w x y i : ℕ} :
    i ∈ (decomp w x y).R ↔ i < w ∧ y.testBit i := by
  simp [decomp]

end Bit
end BQD
end ABD
