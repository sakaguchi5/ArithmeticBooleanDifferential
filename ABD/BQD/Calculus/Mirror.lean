import Mathlib.Data.Finset.Image
import ABD.BQD.Calculus.Core

namespace ABD
namespace BQD

/-- A mirror operation on a finite universe.

The map is required to preserve the universe and be involutive on that universe.
This is abstract enough to model fixed-width bit reversal later. -/
structure Mirror (α : Type u) [DecidableEq α] (U : Finset α) where
  map : α → α
  maps_mem : ∀ {x : α}, x ∈ U → map x ∈ U
  involutive_on : ∀ {x : α}, x ∈ U → map (map x) = x

namespace Mirror

variable {α : Type u} [DecidableEq α] {U : Finset α}

/-- Image of an active set under the mirror map. -/
def image (ρ : Mirror α U) (A : Finset α) : Finset α :=
  A.image ρ.map

/-- Mirroring preserves membership in the common universe. -/
theorem image_subset_U (ρ : Mirror α U) {A : Finset α} (hA : A ⊆ U) :
    ρ.image A ⊆ U := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
  exact ρ.maps_mem (hA hx)

/-- A mirror-pair BQD: compare an active set with its mirror image. -/
def pair (ρ : Mirror α U) (L : Finset α) (hL : L ⊆ U) : Decomp α where
  U := U
  L := L
  R := ρ.image L
  hL := hL
  hR := ρ.image_subset_U hL

end Mirror

namespace Decomp

variable {α : Type u} [DecidableEq α] {U : Finset α}

/-- A BQD whose right active set is the mirror image of its left active set. -/
def IsMirrorPair (ρ : Mirror α U) (D : Decomp α) : Prop :=
  D.U = U ∧ D.R = ρ.image D.L

end Decomp
end BQD
end ABD
