import Mathlib.Data.Finset.Card
import ABD.BQD.Calculus.MetricsLaws
import ABD.BQD.Bit.MirrorComplement
import ABD.BQD.Bit.TransformDecomp

namespace ABD
namespace BQD
namespace Bit

@[simp] theorem bitUniverse_card (w : ℕ) :
    (bitUniverse w).card = w := by
  simp [bitUniverse]

/-- Active and complement positions have total size equal to the width. -/
@[simp] theorem bitActive_card_add_bitComplement_card (w n : ℕ) :
    (bitActive w n).card + (bitComplement w n).card = w := by
  have hdis : Disjoint (bitActive w n) (bitComplement w n) := by
    rw [Finset.disjoint_left]
    intro x hxA hxC
    have hx : x ∈ bitActive w n ∩ bitComplement w n :=
      Finset.mem_inter.mpr ⟨hxA, hxC⟩
    simp at hx
  calc
    (bitActive w n).card + (bitComplement w n).card
        = (bitActive w n ∪ bitComplement w n).card := by
            rw [Finset.card_union_of_disjoint hdis]
    _ = (bitUniverse w).card := by
            rw [bitActive_union_bitComplement_eq_bitUniverse]
    _ = w := by
            simp [bitUniverse]

/-- The complement count is width minus the active-bit count. -/
theorem bitComplement_card_eq_width_sub_bitActive_card (w n : ℕ) :
    (bitComplement w n).card = w - (bitActive w n).card := by
  calc
    (bitComplement w n).card
        = (bitActive w n).card + (bitComplement w n).card - (bitActive w n).card := by
            rw [Nat.add_sub_cancel_left]
    _ = w - (bitActive w n).card := by
            rw [bitActive_card_add_bitComplement_card]

/-- The active/complement split has cardinality equal to the width. -/
@[simp] theorem bitActive_union_bitComplement_card_eq_width (w n : ℕ) :
    (bitActive w n ∪ bitComplement w n).card = w := by
  rw [bitActive_union_bitComplement_eq_bitUniverse]
  simp [bitUniverse]

/-- The complement/active split has cardinality equal to the width. -/
@[simp] theorem bitComplement_union_bitActive_card_eq_width (w n : ℕ) :
    (bitComplement w n ∪ bitActive w n).card = w := by
  rw [bitComplement_union_bitActive_eq_bitUniverse]
  simp [bitUniverse]

/-- A complement pair has Hamming distance equal to the full width. -/
@[simp] theorem complementPair_hammingDistance_eq_width (w n : ℕ) :
    (complementPair w n).hammingDistance = w := by
  rw [(complementPair w n).hammingDistance_eq_exclusive_card]
  rw [complementPair_exclusive_eq_bitUniverse]
  simp [bitUniverse]

/-- A complement pair has xor count equal to the full width. -/
@[simp] theorem complementPair_xorCount_eq_width (w n : ℕ) :
    (complementPair w n).xorCount = w := by
  rw [← (complementPair w n).hammingDistance_eq_xorCount]
  exact complementPair_hammingDistance_eq_width w n

/-- Mirror preserves the cardinality of active bit positions. -/
theorem mirrorActive_card_eq_bitActive_card (w n : ℕ) :
    (mirrorActive w n).card = (bitActive w n).card := by
  have hinj : Set.InjOn (revIndex w) (↑(bitActive w n)) := by
    intro x hx y hy hxy
    exact (mirror w).map_inj_on
      (bitActive_subset_bitUniverse w n hx)
      (bitActive_subset_bitUniverse w n hy)
      hxy
  simpa [mirrorActive, Mirror.image, mirror] using
    (Finset.card_image_of_injOn hinj)

/-- Mirror preserves the cardinality of complement bit positions. -/
theorem mirrorComplement_card_eq_bitComplement_card (w n : ℕ) :
    (mirrorComplement w n).card = (bitComplement w n).card := by
  have hinj : Set.InjOn (revIndex w) (↑(bitComplement w n)) := by
    intro x hx y hy hxy
    exact (mirror w).map_inj_on
      (bitComplement_subset_bitUniverse w n hx)
      (bitComplement_subset_bitUniverse w n hy)
      hxy
  simpa [mirrorComplement, Mirror.image, mirror] using
    (Finset.card_image_of_injOn hinj)

/-- The mirrored active/complement split has cardinality equal to the width. -/
@[simp] theorem mirrorActive_union_mirrorComplement_card_eq_width (w n : ℕ) :
    (mirrorActive w n ∪ mirrorComplement w n).card = w := by
  rw [mirrorActive_union_mirrorComplement_eq_bitUniverse]
  simp [bitUniverse]

end Bit
end BQD
end ABD
