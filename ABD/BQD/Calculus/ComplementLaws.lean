import ABD.BQD.Calculus.Core

namespace ABD
namespace BQD
namespace Decomp

variable {α : Type u} [DecidableEq α]

/-- Complement the left active set inside the common universe. -/
def complementLeft (D : Decomp α) : Decomp α where
  U := D.U
  L := D.U \ D.L
  R := D.R
  hL := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  hR := D.hR

/-- Complement the right active set inside the common universe. -/
def complementRight (D : Decomp α) : Decomp α where
  U := D.U
  L := D.L
  R := D.U \ D.R
  hL := D.hL
  hR := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1

/-- Complement both active sets inside the common universe. -/
def complementBoth (D : Decomp α) : Decomp α where
  U := D.U
  L := D.U \ D.L
  R := D.U \ D.R
  hL := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  hR := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1

@[simp] theorem complementLeft_U (D : Decomp α) :
    D.complementLeft.U = D.U := rfl

@[simp] theorem complementLeft_L (D : Decomp α) :
    D.complementLeft.L = D.U \ D.L := rfl

@[simp] theorem complementLeft_R (D : Decomp α) :
    D.complementLeft.R = D.R := rfl

@[simp] theorem complementRight_U (D : Decomp α) :
    D.complementRight.U = D.U := rfl

@[simp] theorem complementRight_L (D : Decomp α) :
    D.complementRight.L = D.L := rfl

@[simp] theorem complementRight_R (D : Decomp α) :
    D.complementRight.R = D.U \ D.R := rfl

@[simp] theorem complementBoth_U (D : Decomp α) :
    D.complementBoth.U = D.U := rfl

@[simp] theorem complementBoth_L (D : Decomp α) :
    D.complementBoth.L = D.U \ D.L := rfl

@[simp] theorem complementBoth_R (D : Decomp α) :
    D.complementBoth.R = D.U \ D.R := rfl

/-- Complementing the right side swaps `K` with `P`. -/
@[simp] theorem complementRight_K_eq_P (D : Decomp α) :
    D.complementRight.K = D.P := by
  ext x
  change x ∈ D.L ∩ (D.U \ D.R) ↔ x ∈ D.L \ D.R
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxL, hxUR⟩
    exact Finset.mem_sdiff.mpr ⟨hxL, (Finset.mem_sdiff.mp hxUR).2⟩
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxL, hxNotR⟩
    exact Finset.mem_inter.mpr
      ⟨hxL, Finset.mem_sdiff.mpr ⟨D.hL hxL, hxNotR⟩⟩

/-- Complementing the right side swaps `P` with `K`. -/
@[simp] theorem complementRight_P_eq_K (D : Decomp α) :
    D.complementRight.P = D.K := by
  ext x
  change x ∈ D.L \ (D.U \ D.R) ↔ x ∈ D.L ∩ D.R
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxL, hxNotUR⟩
    have hxR : x ∈ D.R := by
      by_contra hxNotR
      exact hxNotUR (Finset.mem_sdiff.mpr ⟨D.hL hxL, hxNotR⟩)
    exact Finset.mem_inter.mpr ⟨hxL, hxR⟩
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxL, hxR⟩
    refine Finset.mem_sdiff.mpr ⟨hxL, ?_⟩
    intro hxUR
    exact (Finset.mem_sdiff.mp hxUR).2 hxR

/-- Complementing the right side swaps `Q` with `Z`. -/
@[simp] theorem complementRight_Q_eq_Z (D : Decomp α) :
    D.complementRight.Q = D.Z := by
  ext x
  change x ∈ (D.U \ D.R) \ D.L ↔ x ∈ D.U \ (D.L ∪ D.R)
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxUR, hxNotL⟩
    rcases Finset.mem_sdiff.mp hxUR with ⟨hxU, hxNotR⟩
    refine Finset.mem_sdiff.mpr ⟨hxU, ?_⟩
    intro hxUnion
    rcases Finset.mem_union.mp hxUnion with hxL | hxR
    · exact hxNotL hxL
    · exact hxNotR hxR
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxU, hxNotUnion⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · refine Finset.mem_sdiff.mpr ⟨hxU, ?_⟩
      intro hxR
      exact hxNotUnion (Finset.mem_union.mpr (Or.inr hxR))
    · intro hxL
      exact hxNotUnion (Finset.mem_union.mpr (Or.inl hxL))

/-- Complementing the right side swaps `Z` with `Q`. -/
@[simp] theorem complementRight_Z_eq_Q (D : Decomp α) :
    D.complementRight.Z = D.Q := by
  ext x
  change x ∈ D.U \ (D.L ∪ (D.U \ D.R)) ↔ x ∈ D.R \ D.L
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxU, hxNotUnion⟩
    have hxNotL : x ∉ D.L := by
      intro hxL
      exact hxNotUnion (Finset.mem_union.mpr (Or.inl hxL))
    have hxR : x ∈ D.R := by
      by_contra hxNotR
      exact hxNotUnion
        (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxU, hxNotR⟩)))
    exact Finset.mem_sdiff.mpr ⟨hxR, hxNotL⟩
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxR, hxNotL⟩
    refine Finset.mem_sdiff.mpr ⟨D.hR hxR, ?_⟩
    intro hxUnion
    rcases Finset.mem_union.mp hxUnion with hxL | hxUR
    · exact hxNotL hxL
    · exact (Finset.mem_sdiff.mp hxUR).2 hxR

/-- Complementing the left side swaps `K` with `Q`. -/
@[simp] theorem complementLeft_K_eq_Q (D : Decomp α) :
    D.complementLeft.K = D.Q := by
  ext x
  change x ∈ (D.U \ D.L) ∩ D.R ↔ x ∈ D.R \ D.L
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxUL, hxR⟩
    exact Finset.mem_sdiff.mpr ⟨hxR, (Finset.mem_sdiff.mp hxUL).2⟩
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxR, hxNotL⟩
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨D.hR hxR, hxNotL⟩, hxR⟩

/-- Complementing the left side swaps `Q` with `K`. -/
@[simp] theorem complementLeft_Q_eq_K (D : Decomp α) :
    D.complementLeft.Q = D.K := by
  ext x
  change x ∈ D.R \ (D.U \ D.L) ↔ x ∈ D.L ∩ D.R
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxR, hxNotUL⟩
    have hxL : x ∈ D.L := by
      by_contra hxNotL
      exact hxNotUL (Finset.mem_sdiff.mpr ⟨D.hR hxR, hxNotL⟩)
    exact Finset.mem_inter.mpr ⟨hxL, hxR⟩
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxL, hxR⟩
    refine Finset.mem_sdiff.mpr ⟨hxR, ?_⟩
    intro hxUL
    exact (Finset.mem_sdiff.mp hxUL).2 hxL

/-- Complementing the left side swaps `P` with `Z`. -/
@[simp] theorem complementLeft_P_eq_Z (D : Decomp α) :
    D.complementLeft.P = D.Z := by
  ext x
  change x ∈ (D.U \ D.L) \ D.R ↔ x ∈ D.U \ (D.L ∪ D.R)
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxUL, hxNotR⟩
    rcases Finset.mem_sdiff.mp hxUL with ⟨hxU, hxNotL⟩
    refine Finset.mem_sdiff.mpr ⟨hxU, ?_⟩
    intro hxUnion
    rcases Finset.mem_union.mp hxUnion with hxL | hxR
    · exact hxNotL hxL
    · exact hxNotR hxR
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxU, hxNotUnion⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · refine Finset.mem_sdiff.mpr ⟨hxU, ?_⟩
      intro hxL
      exact hxNotUnion (Finset.mem_union.mpr (Or.inl hxL))
    · intro hxR
      exact hxNotUnion (Finset.mem_union.mpr (Or.inr hxR))

/-- Complementing the left side swaps `Z` with `P`. -/
@[simp] theorem complementLeft_Z_eq_P (D : Decomp α) :
    D.complementLeft.Z = D.P := by
  ext x
  change x ∈ D.U \ ((D.U \ D.L) ∪ D.R) ↔ x ∈ D.L \ D.R
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxU, hxNotUnion⟩
    have hxNotR : x ∉ D.R := by
      intro hxR
      exact hxNotUnion (Finset.mem_union.mpr (Or.inr hxR))
    have hxL : x ∈ D.L := by
      by_contra hxNotL
      exact hxNotUnion
        (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxU, hxNotL⟩)))
    exact Finset.mem_sdiff.mpr ⟨hxL, hxNotR⟩
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxL, hxNotR⟩
    refine Finset.mem_sdiff.mpr ⟨D.hL hxL, ?_⟩
    intro hxUnion
    rcases Finset.mem_union.mp hxUnion with hxUL | hxR
    · exact (Finset.mem_sdiff.mp hxUL).2 hxL
    · exact hxNotR hxR

/-- Complementing both sides swaps `K` with `Z`. -/
@[simp] theorem complementBoth_K_eq_Z (D : Decomp α) :
    D.complementBoth.K = D.Z := by
  ext x
  change x ∈ (D.U \ D.L) ∩ (D.U \ D.R) ↔ x ∈ D.U \ (D.L ∪ D.R)
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxUL, hxUR⟩
    rcases Finset.mem_sdiff.mp hxUL with ⟨hxU, hxNotL⟩
    rcases Finset.mem_sdiff.mp hxUR with ⟨_hxU, hxNotR⟩
    refine Finset.mem_sdiff.mpr ⟨hxU, ?_⟩
    intro hxUnion
    rcases Finset.mem_union.mp hxUnion with hxL | hxR
    · exact hxNotL hxL
    · exact hxNotR hxR
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxU, hxNotUnion⟩
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_sdiff.mpr ⟨hxU, ?_⟩
      intro hxL
      exact hxNotUnion (Finset.mem_union.mpr (Or.inl hxL))
    · refine Finset.mem_sdiff.mpr ⟨hxU, ?_⟩
      intro hxR
      exact hxNotUnion (Finset.mem_union.mpr (Or.inr hxR))

/-- Complementing both sides swaps `Z` with `K`. -/
@[simp] theorem complementBoth_Z_eq_K (D : Decomp α) :
    D.complementBoth.Z = D.K := by
  ext x
  change x ∈ D.U \ ((D.U \ D.L) ∪ (D.U \ D.R)) ↔ x ∈ D.L ∩ D.R
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxU, hxNotUnion⟩
    have hxL : x ∈ D.L := by
      by_contra hxNotL
      exact hxNotUnion
        (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxU, hxNotL⟩)))
    have hxR : x ∈ D.R := by
      by_contra hxNotR
      exact hxNotUnion
        (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxU, hxNotR⟩)))
    exact Finset.mem_inter.mpr ⟨hxL, hxR⟩
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxL, hxR⟩
    refine Finset.mem_sdiff.mpr ⟨D.hL hxL, ?_⟩
    intro hxUnion
    rcases Finset.mem_union.mp hxUnion with hxUL | hxUR
    · exact (Finset.mem_sdiff.mp hxUL).2 hxL
    · exact (Finset.mem_sdiff.mp hxUR).2 hxR

/-- Complementing both sides swaps `P` with `Q`. -/
@[simp] theorem complementBoth_P_eq_Q (D : Decomp α) :
    D.complementBoth.P = D.Q := by
  ext x
  change x ∈ (D.U \ D.L) \ (D.U \ D.R) ↔ x ∈ D.R \ D.L
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxUL, hxNotUR⟩
    rcases Finset.mem_sdiff.mp hxUL with ⟨hxU, hxNotL⟩
    have hxR : x ∈ D.R := by
      by_contra hxNotR
      exact hxNotUR (Finset.mem_sdiff.mpr ⟨hxU, hxNotR⟩)
    exact Finset.mem_sdiff.mpr ⟨hxR, hxNotL⟩
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxR, hxNotL⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_sdiff.mpr ⟨D.hR hxR, hxNotL⟩
    · intro hxUR
      exact (Finset.mem_sdiff.mp hxUR).2 hxR

/-- Complementing both sides swaps `Q` with `P`. -/
@[simp] theorem complementBoth_Q_eq_P (D : Decomp α) :
    D.complementBoth.Q = D.P := by
  ext x
  change x ∈ (D.U \ D.R) \ (D.U \ D.L) ↔ x ∈ D.L \ D.R
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxUR, hxNotUL⟩
    rcases Finset.mem_sdiff.mp hxUR with ⟨hxU, hxNotR⟩
    have hxL : x ∈ D.L := by
      by_contra hxNotL
      exact hxNotUL (Finset.mem_sdiff.mpr ⟨hxU, hxNotL⟩)
    exact Finset.mem_sdiff.mpr ⟨hxL, hxNotR⟩
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxL, hxNotR⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_sdiff.mpr ⟨D.hL hxL, hxNotR⟩
    · intro hxUL
      exact (Finset.mem_sdiff.mp hxUL).2 hxL

end Decomp
end BQD
end ABD
