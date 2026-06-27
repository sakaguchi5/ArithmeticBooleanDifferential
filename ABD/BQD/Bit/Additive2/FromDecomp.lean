import ABD.BQD.Calculus.Idempotent
import ABD.BQD.Bit.Decomp
import ABD.BQD.Bit.Additive2.NormalForm

namespace ABD
namespace BQD
namespace Bit
namespace Additive2

/-- Build the width-free additive board from any BQD decomposition.

Only the three additive atoms `B/LO/RO` are retained.  The neither atom is not
stored here; it will be recovered later inside `NormalForm c` from the canonical
output universe. -/
def boardOfDecomp (D : Decomp ℕ) : Board where
  B := D.B
  LO := D.LO
  RO := D.RO
  hB_LO := D.B_inter_LO_eq_empty
  hB_RO := D.B_inter_RO_eq_empty
  hLO_RO := D.LO_inter_RO_eq_empty

/-- The additive board associated to the bit decomposition of two naturals at a
chosen working width. -/
def boardOfPair (width x y : ℕ) : Board :=
  boardOfDecomp (decomp width x y)

@[simp] theorem boardOfPair_B (width x y : ℕ) :
    (boardOfPair width x y).B = (decomp width x y).B := rfl

@[simp] theorem boardOfPair_LO (width x y : ℕ) :
    (boardOfPair width x y).LO = (decomp width x y).LO := rfl

@[simp] theorem boardOfPair_RO (width x y : ℕ) :
    (boardOfPair width x y).RO = (decomp width x y).RO := rfl

/-- The active part of a board built from a decomposition lies inside the
decomposition universe. -/
theorem boardOfDecomp_active_subset_U (D : Decomp ℕ) :
    (boardOfDecomp D).active ⊆ D.U := by
  intro x hx
  have hx' : x ∈ D.B ∪ D.LO ∪ D.RO := by
    simpa [boardOfDecomp, Board.active] using hx
  rcases Finset.mem_union.mp hx' with hBL | hRO
  · rcases Finset.mem_union.mp hBL with hB | hLO
    · exact D.B_subset_U hB
    · exact D.LO_subset_U hLO
  · exact D.RO_subset_U hRO

/-- The active part of a pair board lies inside the working bit universe. -/
theorem boardOfPair_active_subset_bitUniverse (width x y : ℕ) :
    (boardOfPair width x y).active ⊆ bitUniverse width := by
  simpa [boardOfPair] using boardOfDecomp_active_subset_U (decomp width x y)

/-- Build a canonical normal form from a width-free board and an actual output
`c`.  The output determines the universe; `hInside` states that the board fits
inside it. -/
def ofBoard {c : ℕ} (G : Board)
    (hAdd : G.candidateC = c)
    (hInside : G.active ⊆ bitUniverse (bitLength c)) :
    NormalForm c where
  board := G
  hAdd := hAdd
  hInside := hInside

/-- Build a canonical normal form from a decomposition whose universe is the
canonical universe of `c`. -/
def ofDecomp {c : ℕ} (D : Decomp ℕ)
    (hU : D.U = bitUniverse (bitLength c))
    (hAdd : (boardOfDecomp D).candidateC = c) :
    NormalForm c :=
  ofBoard (boardOfDecomp D) hAdd (by
    intro x hx
    rw [← hU]
    exact boardOfDecomp_active_subset_U D hx)

/-- Build a canonical normal form from a bit pair, using the canonical width of
`c` as the working width for the input decomposition. -/
def ofPair (x y c : ℕ)
    (hAdd : (boardOfPair (bitLength c) x y).candidateC = c) :
    NormalForm c :=
  ofBoard (boardOfPair (bitLength c) x y) hAdd
    (boardOfPair_active_subset_bitUniverse (bitLength c) x y)

@[simp] theorem ofPair_board (x y c : ℕ)
    (hAdd : (boardOfPair (bitLength c) x y).candidateC = c) :
    (ofPair x y c hAdd).board = boardOfPair (bitLength c) x y := rfl

/-- Soundness specialized to a normal form generated from a bit pair. -/
@[simp] theorem ofPair_add_eq_c (x y c : ℕ)
    (hAdd : (boardOfPair (bitLength c) x y).candidateC = c) :
    (ofPair x y c hAdd).a + (ofPair x y c hAdd).b = c := by
  simpa using NormalForm.add_eq_c (ofPair x y c hAdd)

end Additive2
end Bit
end BQD
end ABD
