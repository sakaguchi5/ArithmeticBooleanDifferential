import ABD.ABD3.Core.All

namespace ABD3

/-- Convert ABD3's Boolean-support disjointness into mathlib's `Disjoint`. -/
theorem finsetDisjoint_of_supportDisjoint {S T : Support}
    (h : Support.Disjoint S T) : Disjoint S T := by
  rw [Finset.disjoint_left]
  intro p hpS hpT
  have hp : p ∈ S ∩ T := Finset.mem_inter.mpr ⟨hpS, hpT⟩
  have hpEmpty : p ∈ (∅ : Support) := by
    rw [← h]
    exact hp
  simp at hpEmpty

/-- If `A` and `C` are disjoint and `B` and `C` are disjoint, then
`A ∪ B` is disjoint from `C`. -/
theorem supportDisjoint_union_left {A B C : Support}
    (hAC : Support.Disjoint A C) (hBC : Support.Disjoint B C) :
    Support.Disjoint (A ∪ B) C := by
  unfold Support.Disjoint
  ext p
  constructor
  · intro hp
    have hleft : p ∈ A ∪ B := (Finset.mem_inter.mp hp).1
    have hC : p ∈ C := (Finset.mem_inter.mp hp).2
    rcases Finset.mem_union.mp hleft with hA | hB
    · have hpAC : p ∈ A ∩ C := Finset.mem_inter.mpr ⟨hA, hC⟩
      have hpEmpty : p ∈ (∅ : Support) := by
            rw [← hAC]
            exact hpAC
      simp at hpEmpty
    · have hpBC : p ∈ B ∩ C := Finset.mem_inter.mpr ⟨hB, hC⟩
      have hpEmpty : p ∈ (∅ : Support) := by
            rw [← hBC]
            exact hpBC
      simp at hpEmpty
  · intro hp
    simp at hp

/-- The radical of a disjoint Boolean union is the product of the radicals. -/
theorem radOfSupport_union_of_disjoint {S T : Support}
    (h : Support.Disjoint S T) :
    radOfSupport (S ∪ T) = radOfSupport S * radOfSupport T := by
  simpa [radOfSupport] using
    (Finset.prod_union (f := fun p : ℕ => p)
      (finsetDisjoint_of_supportDisjoint h))

namespace ABCData

/-- Radical-small view obtained by replacing `radABC` with the block radical product. -/
def BlockProductRadicalSmall (T : ABCData) (P : PowerData) : Prop :=
  (((T.blockRadicalProduct : ℕ) : ℤ) ^ P.N) < ((T.C.val : ℤ) ^ P.M)

/-- Radical-small view in which each block radical is powered separately. -/
def BlockPowerRadicalSmall (T : ABCData) (P : PowerData) : Prop :=
  ((T.radA : ℤ) ^ P.N) * ((T.radB : ℤ) ^ P.N) * ((T.radC : ℤ) ^ P.N) <
    ((T.C.val : ℤ) ^ P.M)

/-- For `ABCData`, the full radical splits as the product of the three block radicals.

This is now a theorem, not a stored view: block disjointness follows from the
primitive positive ABC data, and the union part is definitional. -/
theorem radABC_eq_blockRadicalProduct (T : ABCData) :
    T.radABC = T.blockRadicalProduct := by
  rcases T.supportBlocksDisjoint with ⟨hAB, hAC, hBC⟩
  have hABC : Support.Disjoint (T.supportA ∪ T.supportB) T.supportC :=
    supportDisjoint_union_left hAC hBC
  calc
    T.radABC = radOfSupport ((T.supportA ∪ T.supportB) ∪ T.supportC) := by
      rfl
    _ = radOfSupport (T.supportA ∪ T.supportB) * radOfSupport T.supportC := by
      exact radOfSupport_union_of_disjoint hABC
    _ = (radOfSupport T.supportA * radOfSupport T.supportB) * radOfSupport T.supportC := by
      rw [radOfSupport_union_of_disjoint hAB]
    _ = T.blockRadicalProduct := by
      rfl

/-- The raw radical-small predicate is the block-product radical-small predicate.

The former `BlockRadicalProductView` hypothesis is no longer needed: the block
product decomposition is automatic for `ABCData`. -/
theorem radicalSmall_iff_blockProductRadicalSmall
    (T : ABCData) (P : PowerData) :
    T.RadicalSmall P ↔ T.BlockProductRadicalSmall P := by
  unfold RadicalSmall RadicalSmallInt BlockProductRadicalSmall
  rw [T.radABC_eq_blockRadicalProduct]

/-- Named view of radical-small after the automatic block-product decomposition. -/
def BlockProductView (T : ABCData) (P : PowerData) : Prop :=
  T.BlockProductRadicalSmall P

/-- The fully powered block view records the later target form
`radA^N * radB^N * radC^N < C^M`. -/
def BlockPowerView (T : ABCData) (P : PowerData) : Prop :=
  T.BlockPowerRadicalSmall P

end ABCData
end ABD3
