import ABD.BQD.Calculus.Addition
import ABD.BQD.Calculus.MetricsLaws

namespace ABD
namespace BQD
namespace Decomp

variable {α : Type u} [DecidableEq α]

/-- The generate region lies inside the common universe. -/
theorem Generate_subset_U (D : Decomp α) :
    D.Generate ⊆ D.U := by
  intro x hx
  exact D.B_subset_U (by simpa [Generate] using hx)

/-- The propagate region lies inside the common universe. -/
theorem Propagate_subset_U (D : Decomp α) :
    D.Propagate ⊆ D.U := by
  intro x hx
  change x ∈ D.LO ∪ D.RO at hx
  rcases Finset.mem_union.mp hx with hxLO | hxRO
  · exact D.LO_subset_U hxLO
  · exact D.RO_subset_U hxRO

/-- The kill region lies inside the common universe. -/
theorem Kill_subset_U (D : Decomp α) :
    D.Kill ⊆ D.U := by
  intro x hx
  exact D.N_subset_U (by simpa [Kill] using hx)

/-- Generate and propagate are orthogonal. -/
@[simp] theorem Generate_inter_Propagate_eq_empty (D : Decomp α) :
    D.Generate ∩ D.Propagate = (∅ : Finset α) := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [Generate, Propagate, B, LO, RO, hxL, hxR]

/-- Generate and kill are orthogonal. -/
@[simp] theorem Generate_inter_Kill_eq_empty (D : Decomp α) :
    D.Generate ∩ D.Kill = (∅ : Finset α) := by
  ext x
  by_cases hxU : x ∈ D.U <;>
  by_cases hxL : x ∈ D.L <;>
  by_cases hxR : x ∈ D.R <;>
    simp [Generate, Kill, B, N, hxU, hxL, hxR]

/-- Propagate and kill are orthogonal. -/
@[simp] theorem Propagate_inter_Kill_eq_empty (D : Decomp α) :
    D.Propagate ∩ D.Kill = (∅ : Finset α) := by
  ext x
  by_cases hxU : x ∈ D.U <;>
  by_cases hxL : x ∈ D.L <;>
  by_cases hxR : x ∈ D.R <;>
    simp [Propagate, Kill, LO, RO, N, hxU, hxL, hxR]

/-- Generate and propagate are disjoint. -/
theorem Generate_disjoint_Propagate (D : Decomp α) :
    Disjoint D.Generate D.Propagate :=
  disjoint_of_inter_eq_empty D.Generate_inter_Propagate_eq_empty

/-- Generate and kill are disjoint. -/
theorem Generate_disjoint_Kill (D : Decomp α) :
    Disjoint D.Generate D.Kill :=
  disjoint_of_inter_eq_empty D.Generate_inter_Kill_eq_empty

/-- Propagate and kill are disjoint. -/
theorem Propagate_disjoint_Kill (D : Decomp α) :
    Disjoint D.Propagate D.Kill :=
  disjoint_of_inter_eq_empty D.Propagate_inter_Kill_eq_empty

/-- Generate plus propagate is the active region. -/
@[simp] theorem Generate_union_Propagate_eq_active (D : Decomp α) :
    D.Generate ∪ D.Propagate = D.active := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [Generate, Propagate, B, LO, RO, active, hxL, hxR]

/-- Generate, propagate, and kill split the common universe. -/
@[simp] theorem Generate_union_Propagate_union_Kill_eq_U (D : Decomp α) :
    D.Generate ∪ D.Propagate ∪ D.Kill = D.U := by
  calc
    D.Generate ∪ D.Propagate ∪ D.Kill
        = D.active ∪ D.N := by
            rw [D.Generate_union_Propagate_eq_active, D.Kill_eq_N]
    _ = D.U := D.active_union_N_eq_U

/-- Generate count is the `B` count. -/
@[simp] theorem Generate_card_eq_bCount (D : Decomp α) :
    D.Generate.card = D.bCount := rfl

/-- Propagate count is the Hamming/xor distance. -/
theorem Propagate_card_eq_hammingDistance (D : Decomp α) :
    D.Propagate.card = D.hammingDistance := by
  rw [D.Propagate_eq_exclusive]
  exact D.hammingDistance_eq_exclusive_card.symm

/-- Kill count is the `N` count. -/
@[simp] theorem Kill_card_eq_nCount (D : Decomp α) :
    D.Kill.card = D.nCount := rfl

/-- Sum without incoming carry has cardinality equal to Hamming distance. -/
theorem SumNoCarry_card_eq_hammingDistance (D : Decomp α) :
    D.SumNoCarry.card = D.hammingDistance := by
  rw [D.SumNoCarry_eq_Propagate]
  exact D.Propagate_card_eq_hammingDistance

/-- The active count is generate count plus propagate count. -/
theorem active_card_eq_Generate_card_add_Propagate_card (D : Decomp α) :
    D.active.card = D.Generate.card + D.Propagate.card := by
  calc
    D.active.card = (D.Generate ∪ D.Propagate).card := by
      rw [D.Generate_union_Propagate_eq_active]
    _ = D.Generate.card + D.Propagate.card := by
      exact Finset.card_union_of_disjoint D.Generate_disjoint_Propagate

/-- The universe count is generate plus propagate plus kill. -/
theorem U_card_eq_Generate_card_add_Propagate_card_add_Kill_card (D : Decomp α) :
    D.U.card = D.Generate.card + D.Propagate.card + D.Kill.card := by
  have hGP : (D.Generate ∪ D.Propagate).card =
      D.Generate.card + D.Propagate.card := by
    exact Finset.card_union_of_disjoint D.Generate_disjoint_Propagate
  have hGPK : Disjoint (D.Generate ∪ D.Propagate) D.Kill := by
    exact disjoint_union_left_of_inter_eq_empty
      D.Generate_inter_Kill_eq_empty
      D.Propagate_inter_Kill_eq_empty
  calc
    D.U.card = (D.Generate ∪ D.Propagate ∪ D.Kill).card := by
      rw [D.Generate_union_Propagate_union_Kill_eq_U]
    _ = (D.Generate ∪ D.Propagate).card + D.Kill.card := by
      exact Finset.card_union_of_disjoint hGPK
    _ = D.Generate.card + D.Propagate.card + D.Kill.card := by
      rw [hGP]

end Decomp
end BQD
end ABD
