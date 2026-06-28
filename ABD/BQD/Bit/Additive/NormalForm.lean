import ABD.BQD.Bit.Additive.BitLength
import ABD.BQD.Bit.Additive.Board

namespace ABD
namespace BQD
namespace Bit
namespace Additive

/-- Canonical additive normal form for a fixed output `c`.

The board is width-free.  The output `c` determines the canonical universe
`U(c) = bitUniverse (bitLength c)`.  The neither-active atom `N` is not stored;
it is recovered as the complement of the board's active atoms inside `U(c)`. -/
structure NormalForm (c : ℕ) where
  /-- The underlying width-free three-atom additive board. -/
  board : Board
  /-- The board candidate is the actual output `c`. -/
  hAdd : board.candidateC = c
  /-- The active atoms of the board fit inside the canonical universe of `c`. -/
  hInside : board.active ⊆ bitUniverse (bitLength c)

namespace NormalForm

variable {c : ℕ}

/-- Canonical width of a normal form. -/
def width (_F : NormalForm c) : ℕ :=
  bitLength c

/-- Canonical bit universe of a normal form. -/
def U (_F : NormalForm c) : Finset ℕ :=
  bitUniverse (bitLength c)

/-- Neither-active atom, recovered as the unused part of the canonical universe. -/
def N (F : NormalForm c) : Finset ℕ :=
  F.U \ F.board.active

/-- Both-active atom of the underlying board. -/
def B (F : NormalForm c) : Finset ℕ :=
  F.board.B

/-- Left-only atom of the underlying board. -/
def LO (F : NormalForm c) : Finset ℕ :=
  F.board.LO

/-- Right-only atom of the underlying board. -/
def RO (F : NormalForm c) : Finset ℕ :=
  F.board.RO

/-- Integer value of the both-active atom. -/
def valB (F : NormalForm c) : ℕ :=
  F.board.valB

/-- Integer value of the left-only atom. -/
def valLO (F : NormalForm c) : ℕ :=
  F.board.valLO

/-- Integer value of the right-only atom. -/
def valRO (F : NormalForm c) : ℕ :=
  F.board.valRO

/-- Integer value of the derived neither-active atom. -/
def valN (F : NormalForm c) : ℕ :=
  evalMask F.N

/-- Generated left integer. -/
def a (F : NormalForm c) : ℕ :=
  F.board.a

/-- Generated right integer. -/
def b (F : NormalForm c) : ℕ :=
  F.board.b

/-- Integer value of the `a & b` mask. -/
def andValue (F : NormalForm c) : ℕ :=
  F.board.andValue

/-- Integer value of the `a xor b` mask. -/
def xorValue (F : NormalForm c) : ℕ :=
  F.board.xorValue

/-- Integer value of the `a | b` mask. -/
def orValue (F : NormalForm c) : ℕ :=
  F.board.orValue

/-- The board candidate output. -/
def candidateC (F : NormalForm c) : ℕ :=
  F.board.candidateC

@[simp] theorem width_def (F : NormalForm c) :
    F.width = bitLength c := rfl

@[simp] theorem U_def (F : NormalForm c) :
    F.U = bitUniverse (bitLength c) := rfl

@[simp] theorem N_def (F : NormalForm c) :
    F.N = F.U \ F.board.active := rfl

@[simp] theorem B_def (F : NormalForm c) :
    F.B = F.board.B := rfl

@[simp] theorem LO_def (F : NormalForm c) :
    F.LO = F.board.LO := rfl

@[simp] theorem RO_def (F : NormalForm c) :
    F.RO = F.board.RO := rfl

@[simp] theorem valB_def (F : NormalForm c) :
    F.valB = F.board.valB := rfl

@[simp] theorem valLO_def (F : NormalForm c) :
    F.valLO = F.board.valLO := rfl

@[simp] theorem valRO_def (F : NormalForm c) :
    F.valRO = F.board.valRO := rfl

@[simp] theorem valN_def (F : NormalForm c) :
    F.valN = evalMask F.N := rfl

@[simp] theorem a_def (F : NormalForm c) :
    F.a = F.board.a := rfl

@[simp] theorem b_def (F : NormalForm c) :
    F.b = F.board.b := rfl

@[simp] theorem andValue_def (F : NormalForm c) :
    F.andValue = F.board.andValue := rfl

@[simp] theorem xorValue_def (F : NormalForm c) :
    F.xorValue = F.board.xorValue := rfl

@[simp] theorem orValue_def (F : NormalForm c) :
    F.orValue = F.board.orValue := rfl

@[simp] theorem candidateC_def (F : NormalForm c) :
    F.candidateC = F.board.candidateC := rfl

/-- The active part of a normal form lies inside its canonical universe. -/
theorem active_subset_U (F : NormalForm c) :
    F.board.active ⊆ F.U := by
  simpa [U] using F.hInside

/-- The both-active atom lies inside the canonical universe. -/
theorem B_subset_U (F : NormalForm c) :
    F.board.B ⊆ F.U := by
  intro x hx
  exact F.active_subset_U (by
    simp [Board.active, hx])

/-- The left-only atom lies inside the canonical universe. -/
theorem LO_subset_U (F : NormalForm c) :
    F.board.LO ⊆ F.U := by
  intro x hx
  exact F.active_subset_U (by
    simp [Board.active, hx])

/-- The right-only atom lies inside the canonical universe. -/
theorem RO_subset_U (F : NormalForm c) :
    F.board.RO ⊆ F.U := by
  intro x hx
  exact F.active_subset_U (by
    simp [Board.active, hx])

/-- The derived neither-active atom lies inside the canonical universe. -/
theorem N_subset_U (F : NormalForm c) :
    F.N ⊆ F.U := by
  intro x hx
  exact (Finset.mem_sdiff.mp hx).1

/-- The active part plus the derived neither atom covers the canonical universe. -/
theorem active_union_N_eq_U (F : NormalForm c) :
    F.board.active ∪ F.N = F.U := by
  rw [N]
  exact Finset.union_sdiff_of_subset F.hInside

/-- The three stored atoms and the derived neither atom cover the canonical universe. -/
theorem B_union_LO_union_RO_union_N_eq_U (F : NormalForm c) :
    F.board.B ∪ F.board.LO ∪ F.board.RO ∪ F.N = F.U := by
  calc
    F.board.B ∪ F.board.LO ∪ F.board.RO ∪ F.N
        = F.board.active ∪ F.N := by
            rfl
    _ = F.U := F.active_union_N_eq_U

/-- The stored both-active atom is disjoint from the derived neither atom. -/
@[simp] theorem B_inter_N_eq_empty (F : NormalForm c) :
    F.board.B ∩ F.N = (∅ : Finset ℕ) := by
  rw [N]
  have hB : F.board.B ⊆ F.board.active := by
    simp [Board.active]
  ext x
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty]
  constructor
  · intro hx
    exact hx.2.2 (hB hx.1)
  · intro hx
    cases hx


/-- The stored left-only atom is disjoint from the derived neither atom. -/
@[simp] theorem LO_inter_N_eq_empty (F : NormalForm c) :
    F.board.LO ∩ F.N = (∅ : Finset ℕ) := by
  rw [N]
  have hLO : F.board.LO ⊆ F.board.active := by
    intro x hx
    simp [Board.active, hx]
  ext x
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty]
  constructor
  · intro hx
    exact hx.2.2 (hLO hx.1)
  · intro hx
    cases hx


/-- The stored right-only atom is disjoint from the derived neither atom. -/
@[simp] theorem RO_inter_N_eq_empty (F : NormalForm c) :
    F.board.RO ∩ F.N = (∅ : Finset ℕ) := by
  rw [N]
  have hRO : F.board.RO ⊆ F.board.active := by
    intro x hx
    simp [Board.active, hx]
  ext x
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty]
  constructor
  · intro hx
    exact hx.2.2 (hRO hx.1)
  · intro hx
    cases hx

/-- The candidate output is the actual output `c`. -/
@[simp] theorem candidateC_eq_c (F : NormalForm c) :
    F.candidateC = c := by
  exact F.hAdd

/-- Soundness of the additive normal form: the generated inputs add to `c`. -/
@[simp] theorem add_eq_c (F : NormalForm c) :
    F.a + F.b = c := by
  calc
    F.a + F.b = F.candidateC := by
      simpa [a, b, candidateC] using F.board.add_eq_candidateC
    _ = c := F.hAdd

/-- Normal-form no-overflow, expressed as a board-inside-universe statement. -/
theorem noActiveOverflow (F : NormalForm c) :
    F.board.active ⊆ F.U :=
  F.active_subset_U

end NormalForm
end Additive
end Bit
end BQD
end ABD
