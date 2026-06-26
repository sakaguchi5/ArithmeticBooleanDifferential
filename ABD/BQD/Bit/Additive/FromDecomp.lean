import ABD.BQD.Calculus.Idempotent
import ABD.BQD.Bit.Decomp
import ABD.BQD.Bit.Additive.NormalForm

namespace ABD
namespace BQD
namespace Bit
namespace Additive

/-- Build the pre-normal-form additive board from any BQD decomposition whose
universe is `bitUniverse width`.

This is the bridge from the abstract two-variable BQD calculus to the
Finset-based additive board. -/
def boardOfDecomp (width : ℕ) (D : Decomp ℕ) (hU : D.U = bitUniverse width) :
    Board width where
  B := D.B
  LO := D.LO
  RO := D.RO
  N := D.N
  hB := by
    intro x hx
    rw [← hU]
    exact D.B_subset_U hx
  hLO := by
    intro x hx
    rw [← hU]
    exact D.LO_subset_U hx
  hRO := by
    intro x hx
    rw [← hU]
    exact D.RO_subset_U hx
  hN := by
    intro x hx
    rw [← hU]
    exact D.N_subset_U hx
  hB_LO := D.B_inter_LO_eq_empty
  hB_RO := D.B_inter_RO_eq_empty
  hB_N := D.B_inter_N_eq_empty
  hLO_RO := D.LO_inter_RO_eq_empty
  hLO_N := D.LO_inter_N_eq_empty
  hRO_N := D.RO_inter_N_eq_empty
  hcover := by
    rw [← hU]
    exact D.B_union_LO_union_RO_union_N_eq_U

/-- The additive board associated to the bit decomposition of two naturals at
common width `width`. -/
def boardOfPair (width x y : ℕ) : Board width :=
  boardOfDecomp width (decomp width x y) rfl

@[simp] theorem boardOfPair_B (width x y : ℕ) :
    (boardOfPair width x y).B = (decomp width x y).B := rfl

@[simp] theorem boardOfPair_LO (width x y : ℕ) :
    (boardOfPair width x y).LO = (decomp width x y).LO := rfl

@[simp] theorem boardOfPair_RO (width x y : ℕ) :
    (boardOfPair width x y).RO = (decomp width x y).RO := rfl

@[simp] theorem boardOfPair_N (width x y : ℕ) :
    (boardOfPair width x y).N = (decomp width x y).N := rfl

/-- Build a genuine normal form from a board and an actual output `c`.
The equality `hAdd` connects the board candidate to `c`, and `hC_lt` states
that the output fits inside the common width. -/
def ofBoard {width : ℕ} (G : Board width) (c : ℕ)
    (hAdd : G.candidateC = c) (hC_lt : c < 2 ^ width) :
    NormalForm width where
  board := G
  c := c
  hAdd := hAdd
  hC_lt := hC_lt

/-- Build a genuine normal form from a decomposition, an actual output `c`, and
the two normal-form witnesses. -/
def ofDecomp (width : ℕ) (D : Decomp ℕ) (hU : D.U = bitUniverse width) (c : ℕ)
    (hAdd : (boardOfDecomp width D hU).candidateC = c)
    (hC_lt : c < 2 ^ width) :
    NormalForm width :=
  ofBoard (boardOfDecomp width D hU) c hAdd hC_lt

/-- Build a genuine normal form from a bit pair and an actual output `c`. -/
def ofPair (width x y c : ℕ)
    (hAdd : (boardOfPair width x y).candidateC = c)
    (hC_lt : c < 2 ^ width) :
    NormalForm width :=
  ofBoard (boardOfPair width x y) c hAdd hC_lt

@[simp] theorem ofPair_board (width x y c : ℕ)
    (hAdd : (boardOfPair width x y).candidateC = c)
    (hC_lt : c < 2 ^ width) :
    (ofPair width x y c hAdd hC_lt).board = boardOfPair width x y := rfl

@[simp] theorem ofPair_c (width x y c : ℕ)
    (hAdd : (boardOfPair width x y).candidateC = c)
    (hC_lt : c < 2 ^ width) :
    (ofPair width x y c hAdd hC_lt).c = c := rfl

/-- Soundness specialized to a normal form generated from a bit pair. -/
@[simp] theorem ofPair_add_eq_c (width x y c : ℕ)
    (hAdd : (boardOfPair width x y).candidateC = c)
    (hC_lt : c < 2 ^ width) :
    (ofPair width x y c hAdd hC_lt).a +
      (ofPair width x y c hAdd hC_lt).b = c := by
  simpa using NormalForm.add_eq_c (ofPair width x y c hAdd hC_lt)

/-- A generated pair normal form does not overflow. -/
theorem ofPair_noOverflow (width x y c : ℕ)
    (hAdd : (boardOfPair width x y).candidateC = c)
    (hC_lt : c < 2 ^ width) :
    ¬ (ofPair width x y c hAdd hC_lt).Overflow := by
  exact NormalForm.noOverflow (ofPair width x y c hAdd hC_lt)

end Additive
end Bit
end BQD
end ABD
