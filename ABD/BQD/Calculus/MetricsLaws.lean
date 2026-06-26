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

/-- The active universe splits into the active part and the neither-active quadrant. -/
@[simp] theorem active_union_Z_eq_U (D : Decomp α) :
    D.active ∪ D.Z = D.U := by
  calc
    D.active ∪ D.Z = (D.K ∪ D.P ∪ D.Q) ∪ D.Z := by
      rw [← D.K_union_P_union_Q_eq_active]
    _ = D.U := by
      exact D.K_union_P_union_Q_union_Z_eq_U

/-- The active part and the neither-active quadrant are disjoint. -/
theorem active_disjoint_Z (D : Decomp α) : Disjoint D.active D.Z := by
  rw [← D.K_union_P_union_Q_eq_active]
  exact disjoint_union_union_left_of_inter_eq_empty
    D.K_inter_Z_eq_empty
    D.P_inter_Z_eq_empty
    D.Q_inter_Z_eq_empty

/-- The left active set has size `|K| + |P|`. -/
theorem card_L_eq_kCount_add_pCount (D : Decomp α) :
    D.L.card = D.kCount + D.pCount := by
  calc
    D.L.card = (D.K ∪ D.P).card := by
      rw [D.K_union_P_eq_L]
    _ = D.K.card + D.P.card := by
      exact card_union_of_inter_eq_empty D.K_inter_P_eq_empty
    _ = D.kCount + D.pCount := rfl

/-- The right active set has size `|K| + |Q|`. -/
theorem card_R_eq_kCount_add_qCount (D : Decomp α) :
    D.R.card = D.kCount + D.qCount := by
  calc
    D.R.card = (D.K ∪ D.Q).card := by
      rw [D.K_union_Q_eq_R]
    _ = D.K.card + D.Q.card := by
      exact card_union_of_inter_eq_empty D.K_inter_Q_eq_empty
    _ = D.kCount + D.qCount := rfl

/-- The xor/Hamming region has size `|P| + |Q|`. -/
theorem card_exclusive_eq_pCount_add_qCount (D : Decomp α) :
    D.exclusive.card = D.pCount + D.qCount := by
  calc
    D.exclusive.card = (D.P ∪ D.Q).card := by
      rw [D.exclusive_eq_P_union_Q]
    _ = D.P.card + D.Q.card := by
      exact card_union_of_inter_eq_empty D.P_inter_Q_eq_empty
    _ = D.pCount + D.qCount := rfl

/-- `xorCount` is the cardinality of the exclusive-active region. -/
theorem xorCount_eq_exclusive_card (D : Decomp α) :
    D.xorCount = D.exclusive.card := by
  rw [card_exclusive_eq_pCount_add_qCount]
  rfl

/-- The active union has size `|K| + |P| + |Q|`. -/
theorem card_active_eq_kCount_add_pCount_add_qCount (D : Decomp α) :
    D.active.card = D.kCount + D.pCount + D.qCount := by
  have hKP : (D.K ∪ D.P).card = D.K.card + D.P.card :=
    card_union_of_inter_eq_empty D.K_inter_P_eq_empty
  have hKP_Q : Disjoint (D.K ∪ D.P) D.Q :=
    disjoint_union_left_of_inter_eq_empty
      D.K_inter_Q_eq_empty
      D.P_inter_Q_eq_empty
  calc
    D.active.card = (D.K ∪ D.P ∪ D.Q).card := by
      rw [D.K_union_P_union_Q_eq_active]
    _ = (D.K ∪ D.P).card + D.Q.card := by
      exact Finset.card_union_of_disjoint hKP_Q
    _ = D.kCount + D.pCount + D.qCount := by
      rw [hKP]
      rfl

/-- The common universe has size `|active| + |Z|`. -/
theorem card_U_eq_unionCount_add_zCount (D : Decomp α) :
    D.U.card = D.unionCount + D.zCount := by
  calc
    D.U.card = (D.active ∪ D.Z).card := by
      rw [D.active_union_Z_eq_U]
    _ = D.active.card + D.Z.card := by
      exact Finset.card_union_of_disjoint D.active_disjoint_Z
    _ = D.unionCount + D.zCount := rfl

/-- The common universe has size `|K| + `|P| + `|Q| + `|Z|`. -/
theorem card_U_eq_kCount_add_pCount_add_qCount_add_zCount (D : Decomp α) :
    D.U.card = D.kCount + D.pCount + D.qCount + D.zCount := by
  rw [D.card_U_eq_unionCount_add_zCount]
  rw [show D.unionCount = D.active.card by rfl]
  rw [D.card_active_eq_kCount_add_pCount_add_qCount]

/-- Hamming distance equals the size of the exclusive-active region. -/
theorem hammingDistance_eq_exclusive_card (D : Decomp α) :
    D.hammingDistance = D.exclusive.card := by
  rw [hammingDistance_eq_xorCount]
  exact D.xorCount_eq_exclusive_card

end Decomp
end BQD
end ABD
