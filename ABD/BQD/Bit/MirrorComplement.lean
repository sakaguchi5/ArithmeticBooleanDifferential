import ABD.BQD.Bit.Mirror

namespace ABD
namespace BQD
namespace Bit

/-- Mirror image of the fixed-width complement of `n`. -/
def mirrorComplement (w n : ℕ) : Finset ℕ :=
  (mirror w).image (bitComplement w n)

/-- Mirroring a fixed-width complement is the complement of the mirrored active set. -/
@[simp] theorem mirror_image_bitComplement (w n : ℕ) :
    (mirror w).image (bitComplement w n) = bitUniverse w \ mirrorActive w n := by
  simpa [bitComplement, mirrorActive] using
    (mirror w).image_compl_U (bitActive_subset_bitUniverse w n)

@[simp] theorem mirrorComplement_eq (w n : ℕ) :
    mirrorComplement w n = bitUniverse w \ mirrorActive w n := by
  simp [mirrorComplement]

/-- The mirrored active part and mirrored complement split the common universe. -/
@[simp] theorem mirrorActive_union_mirrorComplement_eq_bitUniverse (w n : ℕ) :
    mirrorActive w n ∪ mirrorComplement w n = bitUniverse w := by
  calc
    mirrorActive w n ∪ mirrorComplement w n
        = (mirror w).image (bitActive w n) ∪ (mirror w).image (bitComplement w n) := rfl
    _ = (mirror w).image (bitActive w n ∪ bitComplement w n) := by
        rw [← (mirror w).image_union (bitActive w n) (bitComplement w n)]
    _ = (mirror w).image (bitUniverse w) := by
        rw [bitActive_union_bitComplement_eq_bitUniverse]
    _ = bitUniverse w := by
        exact (mirror w).image_U_eq_U

/-- The mirrored complement and mirrored active part split the common universe. -/
@[simp] theorem mirrorComplement_union_mirrorActive_eq_bitUniverse (w n : ℕ) :
    mirrorComplement w n ∪ mirrorActive w n = bitUniverse w := by
  rw [Finset.union_comm]
  exact mirrorActive_union_mirrorComplement_eq_bitUniverse w n

/-- The mirrored active part and mirrored complement are disjoint. -/
@[simp] theorem mirrorActive_inter_mirrorComplement_eq_empty (w n : ℕ) :
    mirrorActive w n ∩ mirrorComplement w n = ∅ := by
  ext i
  by_cases hi : i ∈ bitUniverse w
  · rw [mirrorComplement_eq]
    by_cases hm : i ∈ mirrorActive w n
    · simp
    · simp
  · have hma : i ∉ mirrorActive w n := by
      intro h
      exact hi (mirrorActive_subset_bitUniverse w n h)
    have hmc : i ∉ mirrorComplement w n := by
      intro h
      rw [mirrorComplement_eq] at h
      exact hi (Finset.mem_sdiff.mp h).1
    simp

/-- The mirrored complement and mirrored active part are disjoint. -/
@[simp] theorem mirrorComplement_inter_mirrorActive_eq_empty (w n : ℕ) :
    mirrorComplement w n ∩ mirrorActive w n = ∅ := by
  rw [Finset.inter_comm]
  exact mirrorActive_inter_mirrorComplement_eq_empty w n

end Bit
end BQD
end ABD
