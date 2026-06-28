import ABD.BQD.Bit.Additive.NormalForm

namespace ABD
namespace BQD
namespace Bit
namespace Additive

/-- Finset disjointness from an empty intersection. -/
theorem disjoint_of_inter_eq_empty {S T : Finset ℕ}
    (h : S ∩ T = (∅ : Finset ℕ)) : Disjoint S T := by
  rw [Finset.disjoint_left]
  intro x hxS hxT
  have hx : x ∈ S ∩ T := Finset.mem_inter.mpr ⟨hxS, hxT⟩
  simp [h] at hx

/-- A union is disjoint from a third set if both pieces are disjoint from it. -/
theorem disjoint_union_left_of_inter_eq_empty
    {A B C : Finset ℕ}
    (hAC : A ∩ C = (∅ : Finset ℕ))
    (hBC : B ∩ C = (∅ : Finset ℕ)) :
    Disjoint (A ∪ B) C := by
  rw [Finset.disjoint_left]
  intro x hx hC
  rcases Finset.mem_union.mp hx with hA | hB
  · have hxAC : x ∈ A ∩ C := Finset.mem_inter.mpr ⟨hA, hC⟩
    simp [hAC] at hxAC
  · have hxBC : x ∈ B ∩ C := Finset.mem_inter.mpr ⟨hB, hC⟩
    simp [hBC] at hxBC

/-- A three-piece union is disjoint from a fourth set if each piece is. -/
theorem disjoint_union_union_left_of_inter_eq_empty
    {A B C D : Finset ℕ}
    (hAD : A ∩ D = (∅ : Finset ℕ))
    (hBD : B ∩ D = (∅ : Finset ℕ))
    (hCD : C ∩ D = (∅ : Finset ℕ)) :
    Disjoint (A ∪ B ∪ C) D := by
  rw [Finset.disjoint_left]
  intro x hx hD
  rcases Finset.mem_union.mp hx with hAB | hC
  · rcases Finset.mem_union.mp hAB with hA | hB
    · have hxAD : x ∈ A ∩ D := Finset.mem_inter.mpr ⟨hA, hD⟩
      simp [hAD] at hxAD
    · have hxBD : x ∈ B ∩ D := Finset.mem_inter.mpr ⟨hB, hD⟩
      simp [hBD] at hxBD
  · have hxCD : x ∈ C ∩ D := Finset.mem_inter.mpr ⟨hC, hD⟩
    simp [hCD] at hxCD

/-- Integer evaluation sends disjoint unions of bit-position sets to sums. -/
theorem evalMask_union_of_disjoint {S T : Finset ℕ}
    (h : Disjoint S T) :
    evalMask (S ∪ T) = evalMask S + evalMask T := by
  simp [evalMask, Finset.sum_union h]

/-- Integer evaluation of four pairwise-disjoint atoms is the sum of their values. -/
theorem evalMask_four_union_eq_add
    {A B C D : Finset ℕ}
    (hAB : A ∩ B = (∅ : Finset ℕ))
    (hAC : A ∩ C = (∅ : Finset ℕ))
    (hAD : A ∩ D = (∅ : Finset ℕ))
    (hBC : B ∩ C = (∅ : Finset ℕ))
    (hBD : B ∩ D = (∅ : Finset ℕ))
    (hCD : C ∩ D = (∅ : Finset ℕ)) :
    evalMask (A ∪ B ∪ C ∪ D) =
      evalMask A + evalMask B + evalMask C + evalMask D := by
  calc
    evalMask (A ∪ B ∪ C ∪ D)
        = evalMask (A ∪ B ∪ C) + evalMask D := by
            exact evalMask_union_of_disjoint
              (disjoint_union_union_left_of_inter_eq_empty hAD hBD hCD)
    _ = (evalMask (A ∪ B) + evalMask C) + evalMask D := by
            rw [evalMask_union_of_disjoint
              (disjoint_union_left_of_inter_eq_empty hAC hBC)]
    _ = ((evalMask A + evalMask B) + evalMask C) + evalMask D := by
            rw [evalMask_union_of_disjoint (disjoint_of_inter_eq_empty hAB)]
    _ = evalMask A + evalMask B + evalMask C + evalMask D := by
            ac_rfl

/-- Evaluation of the common-width universe: all `width` bits set. -/
@[simp] theorem evalMask_bitUniverse (width : ℕ) :
    evalMask (bitUniverse width) = 2 ^ width - 1 := by
  induction width with
  | zero =>
      simp [evalMask, bitUniverse]
  | succ width ih =>
      simp only [evalMask, bitUniverse, Finset.sum_range_succ] at ih ⊢
      rw [ih, pow_succ]
      omega

namespace NormalForm

variable {c : ℕ}

/-- Evaluation of the canonical universe of a normal form. -/
@[simp] theorem eval_U (F : NormalForm c) :
    evalMask F.U = 2 ^ bitLength c - 1 := by
  simp [NormalForm.U, evalMask_bitUniverse]

/-- The integer value of all four atoms is the value of the canonical universe. -/
theorem eval_cover (F : NormalForm c) :
    F.valB + F.valLO + F.valRO + F.valN = evalMask F.U := by
  rw [← F.B_union_LO_union_RO_union_N_eq_U]
  dsimp [NormalForm.valB, NormalForm.valLO, NormalForm.valRO, NormalForm.valN,
    Board.valB, Board.valLO, Board.valRO]
  symm
  exact evalMask_four_union_eq_add
    F.board.hB_LO F.board.hB_RO F.B_inter_N_eq_empty
    F.board.hLO_RO F.LO_inter_N_eq_empty F.RO_inter_N_eq_empty

/-- The integer value of all four atoms is `2^bitLength c - 1`. -/
@[simp] theorem eval_cover_eq_pow_sub_one (F : NormalForm c) :
    F.valB + F.valLO + F.valRO + F.valN = 2 ^ bitLength c - 1 := by
  rw [F.eval_cover]
  exact F.eval_U

end NormalForm
end Additive
end Bit
end BQD
end ABD
