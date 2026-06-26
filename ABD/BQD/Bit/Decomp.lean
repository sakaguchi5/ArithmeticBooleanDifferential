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

/-- Bit-level BQD decomposition of a number and its fixed-width complement. -/
def complementPair (w n : ℕ) : Decomp ℕ where
  U := bitUniverse w
  L := bitActive w n
  R := bitComplement w n
  hL := bitActive_subset_bitUniverse w n
  hR := bitComplement_subset_bitUniverse w n

@[simp] theorem complementPair_U (w n : ℕ) :
    (complementPair w n).U = bitUniverse w := rfl

@[simp] theorem complementPair_L (w n : ℕ) :
    (complementPair w n).L = bitActive w n := rfl

@[simp] theorem complementPair_R (w n : ℕ) :
    (complementPair w n).R = bitComplement w n := rfl

@[simp] theorem mem_complementPair_left {w n i : ℕ} :
    i ∈ (complementPair w n).L ↔ i < w ∧ n.testBit i := by
  simp [complementPair]

@[simp] theorem mem_complementPair_right {w n i : ℕ} :
    i ∈ (complementPair w n).R ↔ i < w ∧ ¬ n.testBit i := by
  simp [complementPair]

/-- A bit and its fixed-width complement have no both-active positions. -/
@[simp] theorem complementPair_K_eq_empty (w n : ℕ) :
    (complementPair w n).K = ∅ := by
  ext i
  simp [complementPair, Decomp.K]

/-- For a complement pair, left-only is exactly the active bit set. -/
@[simp] theorem complementPair_P_eq_bitActive (w n : ℕ) :
    (complementPair w n).P = bitActive w n := by
  ext i
  by_cases hi : i < w
  · by_cases hb : n.testBit i
    · simp [complementPair, Decomp.P, bitComplement, bitActive, bitUniverse, hi, hb]
    · simp [complementPair, Decomp.P, bitComplement, bitActive, bitUniverse, hi, hb]
  · simp [complementPair, Decomp.P, bitComplement, bitActive, bitUniverse, hi]

/-- For a complement pair, right-only is exactly the complement bit set. -/
@[simp] theorem complementPair_Q_eq_bitComplement (w n : ℕ) :
    (complementPair w n).Q = bitComplement w n := by
  ext i
  by_cases hi : i < w
  · by_cases hb : n.testBit i
    · simp [complementPair, Decomp.Q, bitComplement, bitActive, bitUniverse, hi, hb]
    · simp [complementPair, Decomp.Q, bitComplement, bitActive, bitUniverse, hi, hb]
  · simp [complementPair, Decomp.Q, bitComplement, bitActive, bitUniverse, hi]

/-- A bit and its fixed-width complement have no neither-active positions. -/
@[simp] theorem complementPair_Z_eq_empty (w n : ℕ) :
    (complementPair w n).Z = ∅ := by
  ext i
  by_cases hi : i < w
  · by_cases hb : n.testBit i
    · simp [complementPair, Decomp.Z, bitComplement, bitActive, bitUniverse, hi, hb]
    · simp [complementPair, Decomp.Z, bitComplement, bitActive, bitUniverse, hi, hb]
  · simp [complementPair, Decomp.Z, bitComplement, bitActive, bitUniverse, hi]

/-- A complement pair is active everywhere in the common-width universe. -/
@[simp] theorem complementPair_active_eq_bitUniverse (w n : ℕ) :
    (complementPair w n).active = bitUniverse w := by
  simp [complementPair, Decomp.active]

/-- A complement pair is exclusive everywhere in the common-width universe. -/
@[simp] theorem complementPair_exclusive_eq_bitUniverse (w n : ℕ) :
    (complementPair w n).exclusive = bitUniverse w := by
  simp only [Decomp.exclusive_def, Decomp.P_def, complementPair_L, complementPair_R, Decomp.Q_def]
  ext i
  simp [bitUniverse, bitActive, bitComplement]
  by_cases h : i < w <;> simp [h]

end Bit
end BQD
end ABD
