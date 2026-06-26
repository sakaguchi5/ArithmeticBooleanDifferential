import ABD.BQD.Calculus.Carry
import ABD.BQD.Calculus.AdditionLaws
import Mathlib.Data.Finset.Image

namespace ABD
namespace BQD

/-- A carry-shift operation on a common universe.

This abstracts the later fixed-width bit operation `i ↦ i+1`.  At the BQD
calculus level we only require that the shift sends positions of the common
universe back into the same universe. -/
structure CarryShift (α : Type u) [DecidableEq α] (U : Finset α) where
  map : α → α
  maps_mem : ∀ {x : α}, x ∈ U → map x ∈ U

namespace CarryShift

variable {α : Type u} [DecidableEq α] {U : Finset α}

/-- Image of a set under a carry-shift map. -/
def image (σ : CarryShift α U) (A : Finset α) : Finset α :=
  A.image σ.map

@[simp] theorem image_empty (σ : CarryShift α U) :
    σ.image (∅ : Finset α) = ∅ := by
  ext x
  simp [image]

/-- A carry-shift preserves containment in the common universe. -/
theorem image_subset_U (σ : CarryShift α U) {A : Finset α} (hA : A ⊆ U) :
    σ.image A ⊆ U := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
  exact σ.maps_mem (hA hx)

end CarryShift

namespace Decomp

variable {α : Type u} [DecidableEq α]

/-- The unshifted local carry mask always lies inside the common universe. -/
theorem carryStep_subset_U (D : Decomp α) (incoming : Finset α) :
    D.carryStep incoming ⊆ D.U := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxG | hxPI
  · exact D.Generate_subset_U hxG
  · exact D.Propagate_subset_U (Finset.mem_inter.mp hxPI).1

/-- Shifted carry step: first apply the local carry rule, then move carry
positions by the supplied common-universe-preserving shift. -/
def shiftedCarryStep
    (D : Decomp α) (σ : CarryShift α D.U) (incoming : Finset α) : Finset α :=
  σ.image (D.carryStep incoming)

@[simp] theorem shiftedCarryStep_def
    (D : Decomp α) (σ : CarryShift α D.U) (incoming : Finset α) :
    D.shiftedCarryStep σ incoming =
      σ.image (D.Generate ∪ (D.Propagate ∩ incoming)) := rfl

/-- Shifted carry masks remain inside the common universe. -/
theorem shiftedCarryStep_subset_U
    (D : Decomp α) (σ : CarryShift α D.U) (incoming : Finset α) :
    D.shiftedCarryStep σ incoming ⊆ D.U := by
  exact σ.image_subset_U (D.carryStep_subset_U incoming)

/-- With no incoming carries, the shifted carry is just shifted generate. -/
@[simp] theorem shiftedCarryStep_empty
    (D : Decomp α) (σ : CarryShift α D.U) :
    D.shiftedCarryStep σ ∅ = σ.image D.Generate := by
  calc
    D.shiftedCarryStep σ ∅ = σ.image (D.carryStep ∅) := rfl
    _ = σ.image D.Generate := by rw [D.carryStep_empty]

/-- If no incoming carries hit the propagate region, only generated carries remain. -/
theorem shiftedCarryStep_of_no_propagated_incoming
    (D : Decomp α) (σ : CarryShift α D.U) (incoming : Finset α)
    (h : D.Propagate ∩ incoming = (∅ : Finset α)) :
    D.shiftedCarryStep σ incoming = σ.image D.Generate := by
  rw [shiftedCarryStep, carryStep, h]
  simp [CarryShift.image]

/-- If all incoming carries lie in the propagate region, they all survive the
local propagation step before shifting. -/
theorem shiftedCarryStep_of_incoming_subset_propagate
    (D : Decomp α) (σ : CarryShift α D.U) (incoming : Finset α)
    (h : incoming ⊆ D.Propagate) :
    D.shiftedCarryStep σ incoming = σ.image (D.Generate ∪ incoming) := by
  have hInter : D.Propagate ∩ incoming = incoming := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_inter.mp hx).2
    · intro hx
      exact Finset.mem_inter.mpr ⟨h hx, hx⟩
  rw [shiftedCarryStep, carryStep, hInter]

/-- The shifted carry step is controlled by the active region and the incoming
carry mask. -/
theorem shiftedCarryStep_subset_image_active_union_incoming
    (D : Decomp α) (σ : CarryShift α D.U) (incoming : Finset α) :
    D.shiftedCarryStep σ incoming ⊆ σ.image (D.active ∪ incoming) := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
  have hxStep : x ∈ D.Generate ∪ (D.Propagate ∩ incoming) := by
    simpa [carryStep] using hx
  have hxActiveOrIncoming : x ∈ D.active ∪ incoming := by
    rcases Finset.mem_union.mp hxStep with hxG | hxPI
    · have hxK : x ∈ D.K := by
        simpa [Generate] using hxG
      have hxL : x ∈ D.L := (Finset.mem_inter.mp hxK).1
      have hxActive : x ∈ D.active := by
        simpa [active] using Finset.mem_union.mpr (Or.inl hxL)
      exact Finset.mem_union.mpr (Or.inl hxActive)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mp hxPI).2)
  exact Finset.mem_image.mpr ⟨x, hxActiveOrIncoming, rfl⟩

end Decomp
end BQD
end ABD
