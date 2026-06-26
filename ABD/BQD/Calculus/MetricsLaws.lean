import ABD.BQD.Calculus.Metrics

namespace ABD
namespace BQD
namespace Decomp

variable {α : Type u} [DecidableEq α]
/-
theorem disjoint_of_inter_eq_empty
theorem card_union_of_inter_eq_empty
theorem disjoint_union_left_of_inter_eq_empty
theorem disjoint_union_union_left_of_inter_eq_empty
-/
theorem disjoint_of_inter_eq_empty {s t : Finset α}
    (h : s ∩ t = (∅ : Finset α)) : Disjoint s t := by
  rw [Finset.disjoint_left]
  intro x hs ht
  have hx : x ∈ s ∩ t := Finset.mem_inter.mpr ⟨hs, ht⟩
  simp [h] at hx

theorem card_union_of_inter_eq_empty {s t : Finset α}
    (h : s ∩ t = (∅ : Finset α)) :
    (s ∪ t).card = s.card + t.card := by
  exact Finset.card_union_of_disjoint (disjoint_of_inter_eq_empty h)

theorem disjoint_union_left_of_inter_eq_empty
    {a b c : Finset α}
    (hac : a ∩ c = (∅ : Finset α))
    (hbc : b ∩ c = (∅ : Finset α)) :
    Disjoint (a ∪ b) c := by
  rw [Finset.disjoint_left]
  intro x hx hc
  rcases Finset.mem_union.mp hx with ha | hb
  · have h : x ∈ a ∩ c := Finset.mem_inter.mpr ⟨ha, hc⟩
    simp [hac] at h
  · have h : x ∈ b ∩ c := Finset.mem_inter.mpr ⟨hb, hc⟩
    simp [hbc] at h

theorem disjoint_union_union_left_of_inter_eq_empty
    {a b c d : Finset α}
    (had : a ∩ d = (∅ : Finset α))
    (hbd : b ∩ d = (∅ : Finset α))
    (hcd : c ∩ d = (∅ : Finset α)) :
    Disjoint (a ∪ b ∪ c) d := by
  rw [Finset.disjoint_left]
  intro x hx hd
  rcases Finset.mem_union.mp hx with hxab | hc
  · rcases Finset.mem_union.mp hxab with ha | hb
    · have h : x ∈ a ∩ d := Finset.mem_inter.mpr ⟨ha, hd⟩
      simp [had] at h
    · have h : x ∈ b ∩ d := Finset.mem_inter.mpr ⟨hb, hd⟩
      simp [hbd] at h
  · have h : x ∈ c ∩ d := Finset.mem_inter.mpr ⟨hc, hd⟩
    simp [hcd] at h

/-- The active universe splits into the active part and the neither-active atom. -/
@[simp] theorem active_union_N_eq_U (D : Decomp α) :
    D.active ∪ D.N = D.U := by
  calc
    D.active ∪ D.N = (D.B ∪ D.LO ∪ D.RO) ∪ D.N := by
      rw [← D.B_union_LO_union_RO_eq_active]
    _ = D.U := by
      exact D.B_union_LO_union_RO_union_N_eq_U

/-- The active part and the neither-active atom are disjoint. -/
theorem active_disjoint_N (D : Decomp α) : Disjoint D.active D.N := by
  rw [← D.B_union_LO_union_RO_eq_active]
  exact disjoint_union_union_left_of_inter_eq_empty
    D.B_inter_N_eq_empty
    D.LO_inter_N_eq_empty
    D.RO_inter_N_eq_empty

/-- The left active set has size `|B| + |LO|`. -/
theorem card_L_eq_bCount_add_loCount (D : Decomp α) :
    D.L.card = D.bCount + D.loCount := by
  calc
    D.L.card = (D.B ∪ D.LO).card := by
      rw [D.B_union_LO_eq_L]
    _ = D.B.card + D.LO.card := by
      exact card_union_of_inter_eq_empty D.B_inter_LO_eq_empty
    _ = D.bCount + D.loCount := rfl

/-- The right active set has size `|B| + |RO|`. -/
theorem card_R_eq_bCount_add_roCount (D : Decomp α) :
    D.R.card = D.bCount + D.roCount := by
  calc
    D.R.card = (D.B ∪ D.RO).card := by
      rw [D.B_union_RO_eq_R]
    _ = D.B.card + D.RO.card := by
      exact card_union_of_inter_eq_empty D.B_inter_RO_eq_empty
    _ = D.bCount + D.roCount := rfl

/-- The xor/Hamming region has size `|LO| + |RO|`. -/
theorem card_exclusive_eq_loCount_add_roCount (D : Decomp α) :
    D.exclusive.card = D.loCount + D.roCount := by
  calc
    D.exclusive.card = (D.LO ∪ D.RO).card := by
      rw [D.exclusive_eq_LO_union_RO]
    _ = D.LO.card + D.RO.card := by
      exact card_union_of_inter_eq_empty D.LO_inter_RO_eq_empty
    _ = D.loCount + D.roCount := rfl

/-- `xorCount` is the cardinality of the exclusive-active region. -/
theorem xorCount_eq_exclusive_card (D : Decomp α) :
    D.xorCount = D.exclusive.card := by
  rw [card_exclusive_eq_loCount_add_roCount]
  rfl

/-- The active union has size `|B| + |LO| + |RO|`. -/
theorem card_active_eq_bCount_add_loCount_add_roCount (D : Decomp α) :
    D.active.card = D.bCount + D.loCount + D.roCount := by
  have hBLO : (D.B ∪ D.LO).card = D.B.card + D.LO.card :=
    card_union_of_inter_eq_empty D.B_inter_LO_eq_empty
  have hBLO_RO : Disjoint (D.B ∪ D.LO) D.RO :=
    disjoint_union_left_of_inter_eq_empty
      D.B_inter_RO_eq_empty
      D.LO_inter_RO_eq_empty
  calc
    D.active.card = (D.B ∪ D.LO ∪ D.RO).card := by
      rw [D.B_union_LO_union_RO_eq_active]
    _ = (D.B ∪ D.LO).card + D.RO.card := by
      exact Finset.card_union_of_disjoint hBLO_RO
    _ = D.bCount + D.loCount + D.roCount := by
      rw [hBLO]
      rfl

/-- The common universe has size `|active| + |N|`. -/
theorem card_U_eq_unionCount_add_nCount (D : Decomp α) :
    D.U.card = D.unionCount + D.nCount := by
  calc
    D.U.card = (D.active ∪ D.N).card := by
      rw [D.active_union_N_eq_U]
    _ = D.active.card + D.N.card := by
      exact Finset.card_union_of_disjoint D.active_disjoint_N
    _ = D.unionCount + D.nCount := rfl

/-- The common universe has size `|B| + `|LO| + `|RO| + `|N|`. -/
theorem card_U_eq_bCount_add_loCount_add_roCount_add_nCount (D : Decomp α) :
    D.U.card = D.bCount + D.loCount + D.roCount + D.nCount := by
  rw [D.card_U_eq_unionCount_add_nCount]
  rw [show D.unionCount = D.active.card by rfl]
  rw [D.card_active_eq_bCount_add_loCount_add_roCount]

/-- Hamming distance equals the size of the exclusive-active region. -/
theorem hammingDistance_eq_exclusive_card (D : Decomp α) :
    D.hammingDistance = D.exclusive.card := by
  rw [hammingDistance_eq_xorCount]
  exact D.xorCount_eq_exclusive_card

end Decomp
end BQD
end ABD
