import ABD.BQD.Bit.Additive.Board

namespace ABD
namespace BQD
namespace Bit
namespace Additive

/-- Additive bit normal form.

A `Board` is only the pre-normal-form four-region bit board.  A
`NormalForm` additionally chooses an actual target integer `c`, proves that
it is the board's additive candidate `(a xor b) + 2 * (a & b)`, and requires
that this `c` fits inside the common width.

Thus overflow is not an extra hypothesis for normal forms; it is ruled out by
`hC_lt`. -/
structure NormalForm (width : ℕ) where
  /-- The underlying four-region additive board. -/
  board : Board width
  /-- The actual additive output represented by this normal form. -/
  c : ℕ
  /-- The board candidate is the actual output. -/
  hAdd : board.candidateC = c
  /-- The output fits inside the common width. -/
  hC_lt : c < 2 ^ width

namespace NormalForm

variable {width : ℕ}

/-- Both-active atom of the underlying board. -/
def B (F : NormalForm width) : Finset ℕ :=
  F.board.B

/-- Left-only atom of the underlying board. -/
def LO (F : NormalForm width) : Finset ℕ :=
  F.board.LO

/-- Right-only atom of the underlying board. -/
def RO (F : NormalForm width) : Finset ℕ :=
  F.board.RO

/-- Neither-active atom of the underlying board. -/
def N (F : NormalForm width) : Finset ℕ :=
  F.board.N

/-- Integer value of the both-active atom. -/
def valB (F : NormalForm width) : ℕ :=
  F.board.valB

/-- Integer value of the left-only atom. -/
def valLO (F : NormalForm width) : ℕ :=
  F.board.valLO

/-- Integer value of the right-only atom. -/
def valRO (F : NormalForm width) : ℕ :=
  F.board.valRO

/-- Integer value of the neither-active atom. -/
def valN (F : NormalForm width) : ℕ :=
  F.board.valN

/-- Generated left integer. -/
def a (F : NormalForm width) : ℕ :=
  F.board.a

/-- Generated right integer. -/
def b (F : NormalForm width) : ℕ :=
  F.board.b

/-- Integer value of the `a & b` mask. -/
def andValue (F : NormalForm width) : ℕ :=
  F.board.andValue

/-- Integer value of the `a xor b` mask. -/
def xorValue (F : NormalForm width) : ℕ :=
  F.board.xorValue

/-- Integer value of the `a | b` mask. -/
def orValue (F : NormalForm width) : ℕ :=
  F.board.orValue

/-- The board candidate output. -/
def candidateC (F : NormalForm width) : ℕ :=
  F.board.candidateC

@[simp] theorem B_def (F : NormalForm width) :
    F.B = F.board.B := rfl

@[simp] theorem LO_def (F : NormalForm width) :
    F.LO = F.board.LO := rfl

@[simp] theorem RO_def (F : NormalForm width) :
    F.RO = F.board.RO := rfl

@[simp] theorem N_def (F : NormalForm width) :
    F.N = F.board.N := rfl

@[simp] theorem valB_def (F : NormalForm width) :
    F.valB = F.board.valB := rfl

@[simp] theorem valLO_def (F : NormalForm width) :
    F.valLO = F.board.valLO := rfl

@[simp] theorem valRO_def (F : NormalForm width) :
    F.valRO = F.board.valRO := rfl

@[simp] theorem valN_def (F : NormalForm width) :
    F.valN = F.board.valN := rfl

@[simp] theorem a_def (F : NormalForm width) :
    F.a = F.board.a := rfl

@[simp] theorem b_def (F : NormalForm width) :
    F.b = F.board.b := rfl

@[simp] theorem andValue_def (F : NormalForm width) :
    F.andValue = F.board.andValue := rfl

@[simp] theorem xorValue_def (F : NormalForm width) :
    F.xorValue = F.board.xorValue := rfl

@[simp] theorem orValue_def (F : NormalForm width) :
    F.orValue = F.board.orValue := rfl

@[simp] theorem candidateC_def (F : NormalForm width) :
    F.candidateC = F.board.candidateC := rfl

/-- The candidate output is the actual output `c`. -/
@[simp] theorem candidateC_eq_c (F : NormalForm width) :
    F.candidateC = F.c := by
  exact F.hAdd

/-- Soundness of the additive normal form: the generated inputs add to `c`. -/
@[simp] theorem add_eq_c (F : NormalForm width) :
    F.a + F.b = F.c := by
  calc
    F.a + F.b = F.candidateC := by
      simpa [a, b, candidateC] using F.board.add_eq_candidateC
    _ = F.c := F.hAdd

/-- Overflow predicate for a normal form.  This is impossible by `hC_lt`. -/
def Overflow (F : NormalForm width) : Prop :=
  2 ^ width ≤ F.c

/-- The represented output fits in the common width. -/
@[simp] theorem c_lt_two_pow (F : NormalForm width) :
    F.c < 2 ^ width :=
  F.hC_lt

/-- Normal forms do not overflow. -/
theorem noOverflow (F : NormalForm width) :
    ¬ F.Overflow := by
  exact not_le_of_gt F.hC_lt

end NormalForm
end Additive
end Bit
end BQD
end ABD
