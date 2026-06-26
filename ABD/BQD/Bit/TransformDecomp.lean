import ABD.BQD.Calculus.ComplementLaws
import ABD.BQD.Bit.Decomp

namespace ABD
namespace BQD
namespace Bit

/-- Compare the fixed-width complement of the left input with the right input. -/
def decompComplementLeft (w x y : ℕ) : Decomp ℕ :=
  (decomp w x y).complementLeft

/-- Compare the left input with the fixed-width complement of the right input. -/
def decompComplementRight (w x y : ℕ) : Decomp ℕ :=
  (decomp w x y).complementRight

/-- Compare the fixed-width complements of both inputs. -/
def decompComplementBoth (w x y : ℕ) : Decomp ℕ :=
  (decomp w x y).complementBoth

@[simp] theorem decompComplementLeft_U (w x y : ℕ) :
    (decompComplementLeft w x y).U = bitUniverse w := rfl

@[simp] theorem decompComplementLeft_L (w x y : ℕ) :
    (decompComplementLeft w x y).L = bitComplement w x := rfl

@[simp] theorem decompComplementLeft_R (w x y : ℕ) :
    (decompComplementLeft w x y).R = bitActive w y := rfl

@[simp] theorem decompComplementRight_U (w x y : ℕ) :
    (decompComplementRight w x y).U = bitUniverse w := rfl

@[simp] theorem decompComplementRight_L (w x y : ℕ) :
    (decompComplementRight w x y).L = bitActive w x := rfl

@[simp] theorem decompComplementRight_R (w x y : ℕ) :
    (decompComplementRight w x y).R = bitComplement w y := rfl

@[simp] theorem decompComplementBoth_U (w x y : ℕ) :
    (decompComplementBoth w x y).U = bitUniverse w := rfl

@[simp] theorem decompComplementBoth_L (w x y : ℕ) :
    (decompComplementBoth w x y).L = bitComplement w x := rfl

@[simp] theorem decompComplementBoth_R (w x y : ℕ) :
    (decompComplementBoth w x y).R = bitComplement w y := rfl

/-- In `(~x, y)`, the both-active quadrant is the original `Q`. -/
@[simp] theorem decompComplementLeft_K_eq_Q (w x y : ℕ) :
    (decompComplementLeft w x y).K = (decomp w x y).Q := by
  exact (decomp w x y).complementLeft_K_eq_Q

/-- In `(~x, y)`, the right-only quadrant is the original `K`. -/
@[simp] theorem decompComplementLeft_Q_eq_K (w x y : ℕ) :
    (decompComplementLeft w x y).Q = (decomp w x y).K := by
  exact (decomp w x y).complementLeft_Q_eq_K

/-- In `(~x, y)`, the left-only quadrant is the original `Z`. -/
@[simp] theorem decompComplementLeft_P_eq_Z (w x y : ℕ) :
    (decompComplementLeft w x y).P = (decomp w x y).Z := by
  exact (decomp w x y).complementLeft_P_eq_Z

/-- In `(~x, y)`, the neither-active quadrant is the original `P`. -/
@[simp] theorem decompComplementLeft_Z_eq_P (w x y : ℕ) :
    (decompComplementLeft w x y).Z = (decomp w x y).P := by
  exact (decomp w x y).complementLeft_Z_eq_P

/-- In `(x, ~y)`, the both-active quadrant is the original `P`. -/
@[simp] theorem decompComplementRight_K_eq_P (w x y : ℕ) :
    (decompComplementRight w x y).K = (decomp w x y).P := by
  exact (decomp w x y).complementRight_K_eq_P

/-- In `(x, ~y)`, the left-only quadrant is the original `K`. -/
@[simp] theorem decompComplementRight_P_eq_K (w x y : ℕ) :
    (decompComplementRight w x y).P = (decomp w x y).K := by
  exact (decomp w x y).complementRight_P_eq_K

/-- In `(x, ~y)`, the right-only quadrant is the original `Z`. -/
@[simp] theorem decompComplementRight_Q_eq_Z (w x y : ℕ) :
    (decompComplementRight w x y).Q = (decomp w x y).Z := by
  exact (decomp w x y).complementRight_Q_eq_Z

/-- In `(x, ~y)`, the neither-active quadrant is the original `Q`. -/
@[simp] theorem decompComplementRight_Z_eq_Q (w x y : ℕ) :
    (decompComplementRight w x y).Z = (decomp w x y).Q := by
  exact (decomp w x y).complementRight_Z_eq_Q

/-- In `(~x, ~y)`, the both-active quadrant is the original `Z`. -/
@[simp] theorem decompComplementBoth_K_eq_Z (w x y : ℕ) :
    (decompComplementBoth w x y).K = (decomp w x y).Z := by
  exact (decomp w x y).complementBoth_K_eq_Z

/-- In `(~x, ~y)`, the neither-active quadrant is the original `K`. -/
@[simp] theorem decompComplementBoth_Z_eq_K (w x y : ℕ) :
    (decompComplementBoth w x y).Z = (decomp w x y).K := by
  exact (decomp w x y).complementBoth_Z_eq_K

/-- In `(~x, ~y)`, the left-only quadrant is the original `Q`. -/
@[simp] theorem decompComplementBoth_P_eq_Q (w x y : ℕ) :
    (decompComplementBoth w x y).P = (decomp w x y).Q := by
  exact (decomp w x y).complementBoth_P_eq_Q

/-- In `(~x, ~y)`, the right-only quadrant is the original `P`. -/
@[simp] theorem decompComplementBoth_Q_eq_P (w x y : ℕ) :
    (decompComplementBoth w x y).Q = (decomp w x y).P := by
  exact (decomp w x y).complementBoth_Q_eq_P

end Bit
end BQD
end ABD
