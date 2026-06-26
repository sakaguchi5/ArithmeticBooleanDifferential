import ABD.BQD.Calculus.MirrorLaws
import ABD.BQD.Bit.Active
import ABD.BQD.Bit.Reverse

namespace ABD
namespace BQD
namespace Bit

/-- The fixed-width bit mirror induced by `revIndex w`. -/
def mirror (w : ℕ) : Mirror ℕ (bitUniverse w) where
  map := revIndex w
  maps_mem := by
    intro x hx
    exact revIndex_mem_bitUniverse hx
  involutive_on := by
    intro x hx
    exact revIndex_involutive_on_bitUniverse hx

/-- Mirror image of the active bit positions of `n`. -/
def mirrorActive (w n : ℕ) : Finset ℕ :=
  (mirror w).image (bitActive w n)

/-- Mirrored active bit positions remain inside the common-width bit universe. -/
theorem mirrorActive_subset_bitUniverse (w n : ℕ) :
    mirrorActive w n ⊆ bitUniverse w := by
  exact (mirror w).image_subset_U (bitActive_subset_bitUniverse w n)

/-- The canonical mirror-pair BQD for a natural number at width `w`. -/
def mirrorPair (w n : ℕ) : Decomp ℕ :=
  (mirror w).pair (bitActive w n) (bitActive_subset_bitUniverse w n)

@[simp] theorem mirrorPair_U (w n : ℕ) :
    (mirrorPair w n).U = bitUniverse w := rfl

@[simp] theorem mirrorPair_L (w n : ℕ) :
    (mirrorPair w n).L = bitActive w n := rfl

@[simp] theorem mirrorPair_R (w n : ℕ) :
    (mirrorPair w n).R = mirrorActive w n := rfl

/-- In a bit mirror pair, `K` is mirror-fixed. -/
@[simp] theorem mirrorPair_image_K (w n : ℕ) :
    (mirror w).image ((mirrorPair w n).K) = (mirrorPair w n).K := by
  exact Decomp.mirrorPair_image_K (mirror w) (bitActive w n) (bitActive_subset_bitUniverse w n)

/-- In a bit mirror pair, `P` maps to `Q`. -/
@[simp] theorem mirrorPair_image_P (w n : ℕ) :
    (mirror w).image ((mirrorPair w n).P) = (mirrorPair w n).Q := by
  exact Decomp.mirrorPair_image_P (mirror w) (bitActive w n) (bitActive_subset_bitUniverse w n)

/-- In a bit mirror pair, `Q` maps to `P`. -/
@[simp] theorem mirrorPair_image_Q (w n : ℕ) :
    (mirror w).image ((mirrorPair w n).Q) = (mirrorPair w n).P := by
  exact Decomp.mirrorPair_image_Q (mirror w) (bitActive w n) (bitActive_subset_bitUniverse w n)

/-- In a bit mirror pair, `Z` is mirror-fixed. -/
@[simp] theorem mirrorPair_image_Z (w n : ℕ) :
    (mirror w).image ((mirrorPair w n).Z) = (mirrorPair w n).Z := by
  exact Decomp.mirrorPair_image_Z (mirror w) (bitActive w n) (bitActive_subset_bitUniverse w n)

end Bit
end BQD
end ABD
