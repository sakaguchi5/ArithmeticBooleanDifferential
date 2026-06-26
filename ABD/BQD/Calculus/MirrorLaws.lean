import ABD.BQD.Calculus.Mirror

namespace ABD
namespace BQD

namespace Mirror

variable {α : Type u} [DecidableEq α] {U : Finset α}

/-- On the common universe, the mirror map is injective. -/
theorem map_inj_on
    (ρ : Mirror α U) {x y : α} (hx : x ∈ U) (hy : y ∈ U)
    (hxy : ρ.map x = ρ.map y) :
    x = y := by
  calc
    x = ρ.map (ρ.map x) := (ρ.involutive_on hx).symm
    _ = ρ.map (ρ.map y) := by rw [hxy]
    _ = y := ρ.involutive_on hy

/-- Mirroring the whole universe returns the whole universe. -/
@[simp] theorem image_U_eq_U
    (ρ : Mirror α U) :
    ρ.image U = U := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hxU, rfl⟩
    exact ρ.maps_mem hxU
  · intro hyU
    refine Finset.mem_image.mpr ⟨ρ.map y, ρ.maps_mem hyU, ?_⟩
    exact ρ.involutive_on hyU

/-- Mirroring twice returns the original active set, as long as the active set
lies inside the common universe. -/
@[simp] theorem image_image_eq_self
    (ρ : Mirror α U) {A : Finset α} (hA : A ⊆ U) :
    ρ.image (ρ.image A) = A := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    rw [ρ.involutive_on (hA hz)]
    exact hz
  · intro hy
    refine Finset.mem_image.mpr ⟨ρ.map y, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    · exact ρ.involutive_on (hA hy)

/-- Mirror image distributes over union. -/
theorem image_union
    (ρ : Mirror α U) (A B : Finset α) :
    ρ.image (A ∪ B) = ρ.image A ∪ ρ.image B := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_image.mpr ⟨x, hxA, rfl⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr ⟨x, hxB, rfl⟩))
  · intro hy
    rcases Finset.mem_union.mp hy with hyA | hyB
    · rcases Finset.mem_image.mp hyA with ⟨x, hxA, rfl⟩
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_union.mpr (Or.inl hxA), rfl⟩
    · rcases Finset.mem_image.mp hyB with ⟨x, hxB, rfl⟩
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_union.mpr (Or.inr hxB), rfl⟩

/-- Mirror image distributes over intersection for sets inside the common universe. -/
theorem image_inter
    (ρ : Mirror α U) {A B : Finset α} (hA : A ⊆ U) (hB : B ⊆ U) :
    ρ.image (A ∩ B) = ρ.image A ∩ ρ.image B := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases Finset.mem_inter.mp hx with ⟨hxA, hxB⟩
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨x, hxA, rfl⟩,
       Finset.mem_image.mpr ⟨x, hxB, rfl⟩⟩
  · intro hy
    rcases Finset.mem_inter.mp hy with ⟨hyA, hyB⟩
    rcases Finset.mem_image.mp hyA with ⟨x, hxA, hxmap⟩
    rcases Finset.mem_image.mp hyB with ⟨z, hzB, hzmap⟩
    have hx_eq_z : x = z := by
      exact ρ.map_inj_on (hA hxA) (hB hzB) (by rw [hxmap, hzmap])
    have hxB : x ∈ B := by
      simpa [hx_eq_z] using hzB
    exact Finset.mem_image.mpr
      ⟨x, Finset.mem_inter.mpr ⟨hxA, hxB⟩, hxmap⟩

/-- Mirror image distributes over set difference for sets inside the common universe. -/
theorem image_sdiff
    (ρ : Mirror α U) {A B : Finset α} (hA : A ⊆ U) (hB : B ⊆ U) :
    ρ.image (A \ B) = ρ.image A \ ρ.image B := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases Finset.mem_sdiff.mp hx with ⟨hxA, hxNotB⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨x, hxA, rfl⟩, ?_⟩
    intro hbad
    rcases Finset.mem_image.mp hbad with ⟨z, hzB, hzmap⟩
    have hx_eq_z : x = z := by
      exact ρ.map_inj_on (hA hxA) (hB hzB) hzmap.symm
    exact hxNotB (by simpa [hx_eq_z] using hzB)
  · intro hy
    rcases Finset.mem_sdiff.mp hy with ⟨hyA, hyNotB⟩
    rcases Finset.mem_image.mp hyA with ⟨x, hxA, hxmap⟩
    refine Finset.mem_image.mpr ⟨x, ?_, hxmap⟩
    refine Finset.mem_sdiff.mpr ⟨hxA, ?_⟩
    intro hxB
    exact hyNotB (Finset.mem_image.mpr ⟨x, hxB, hxmap⟩)

/-- Mirror image of the complement inside `U`. -/
theorem image_compl_U
    (ρ : Mirror α U) {A : Finset α} (hA : A ⊆ U) :
    ρ.image (U \ A) = U \ ρ.image A := by
  calc
    ρ.image (U \ A) = ρ.image U \ ρ.image A := by
      exact ρ.image_sdiff (by intro x hx; exact hx) hA
    _ = U \ ρ.image A := by
      rw [ρ.image_U_eq_U]

/-- In a mirror pair, the both-active region is fixed by the mirror. -/
theorem image_inter_image_eq_inter_image
    (ρ : Mirror α U) (L : Finset α) (hL : L ⊆ U) :
    ρ.image (L ∩ ρ.image L) = L ∩ ρ.image L := by
  calc
    ρ.image (L ∩ ρ.image L)
        = ρ.image L ∩ ρ.image (ρ.image L) := by
            exact ρ.image_inter hL (ρ.image_subset_U hL)
    _ = ρ.image L ∩ L := by
            rw [ρ.image_image_eq_self hL]
    _ = L ∩ ρ.image L := by
            rw [Finset.inter_comm]

/-- In a mirror pair, the left-only quadrant mirrors to the right-only quadrant. -/
theorem image_leftOnly_eq_rightOnly
    (ρ : Mirror α U) (L : Finset α) (hL : L ⊆ U) :
    ρ.image (L \ ρ.image L) = ρ.image L \ L := by
  calc
    ρ.image (L \ ρ.image L)
        = ρ.image L \ ρ.image (ρ.image L) := by
            exact ρ.image_sdiff hL (ρ.image_subset_U hL)
    _ = ρ.image L \ L := by
            rw [ρ.image_image_eq_self hL]

/-- In a mirror pair, the right-only quadrant mirrors to the left-only quadrant. -/
theorem image_rightOnly_eq_leftOnly
    (ρ : Mirror α U) (L : Finset α) (hL : L ⊆ U) :
    ρ.image (ρ.image L \ L) = L \ ρ.image L := by
  calc
    ρ.image (ρ.image L \ L)
        = ρ.image (ρ.image L \ ρ.image (ρ.image L)) := by
            rw [ρ.image_image_eq_self hL]
    _ = ρ.image (ρ.image L) \ ρ.image L := by
            simpa using ρ.image_leftOnly_eq_rightOnly (ρ.image L) (ρ.image_subset_U hL)
    _ = L \ ρ.image L := by
            rw [ρ.image_image_eq_self hL]

/-- In a mirror pair, the neither-active quadrant is fixed by the mirror. -/
theorem image_neither_eq_neither
    (ρ : Mirror α U) (L : Finset α) (hL : L ⊆ U) :
    ρ.image (U \ (L ∪ ρ.image L)) = U \ (L ∪ ρ.image L) := by
  have hUnion : L ∪ ρ.image L ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxL | hxImg
    · exact hL hxL
    · exact ρ.image_subset_U hL hxImg
  calc
    ρ.image (U \ (L ∪ ρ.image L))
        = U \ ρ.image (L ∪ ρ.image L) := by
            simpa using ρ.image_compl_U hUnion
    _ = U \ (ρ.image L ∪ ρ.image (ρ.image L)) := by
            rw [ρ.image_union L (ρ.image L)]
    _ = U \ (ρ.image L ∪ L) := by
            rw [ρ.image_image_eq_self hL]
    _ = U \ (L ∪ ρ.image L) := by
            rw [Finset.union_comm]

end Mirror

namespace Decomp

variable {α : Type u} [DecidableEq α] {U : Finset α}

/-- For the canonical mirror pair `BQD(L, mirror L)`, the `K` quadrant is mirror-fixed. -/
@[simp] theorem mirrorPair_image_K
    (ρ : Mirror α U) (L : Finset α) (hL : L ⊆ U) :
    ρ.image ((ρ.pair L hL).K) = (ρ.pair L hL).K := by
  simpa [Mirror.pair, K] using ρ.image_inter_image_eq_inter_image L hL

/-- For the canonical mirror pair `BQD(L, mirror L)`, the `P` quadrant maps to `Q`. -/
@[simp] theorem mirrorPair_image_P
    (ρ : Mirror α U) (L : Finset α) (hL : L ⊆ U) :
    ρ.image ((ρ.pair L hL).P) = (ρ.pair L hL).Q := by
  simpa [Mirror.pair, P, Q] using ρ.image_leftOnly_eq_rightOnly L hL

/-- For the canonical mirror pair `BQD(L, mirror L)`, the `Q` quadrant maps to `P`. -/
@[simp] theorem mirrorPair_image_Q
    (ρ : Mirror α U) (L : Finset α) (hL : L ⊆ U) :
    ρ.image ((ρ.pair L hL).Q) = (ρ.pair L hL).P := by
  simpa [Mirror.pair, P, Q] using ρ.image_rightOnly_eq_leftOnly L hL

/-- For the canonical mirror pair `BQD(L, mirror L)`, the `Z` quadrant is mirror-fixed. -/
@[simp] theorem mirrorPair_image_Z
    (ρ : Mirror α U) (L : Finset α) (hL : L ⊆ U) :
    ρ.image ((ρ.pair L hL).Z) = (ρ.pair L hL).Z := by
  simpa [Mirror.pair, Z] using ρ.image_neither_eq_neither L hL

end Decomp
end BQD
end ABD
