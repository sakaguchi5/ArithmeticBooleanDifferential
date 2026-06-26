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

/-- In `(~x, y)`, the both-active atom is the original `RO`. -/
@[simp] theorem decompComplementLeft_B_eq_RO (w x y : ℕ) :
    (decompComplementLeft w x y).B = (decomp w x y).RO := by
  exact (decomp w x y).complementLeft_B_eq_RO

/-- In `(~x, y)`, the right-only atom is the original `B`. -/
@[simp] theorem decompComplementLeft_RO_eq_B (w x y : ℕ) :
    (decompComplementLeft w x y).RO = (decomp w x y).B := by
  exact (decomp w x y).complementLeft_RO_eq_B

/-- In `(~x, y)`, the left-only atom is the original `N`. -/
@[simp] theorem decompComplementLeft_LO_eq_N (w x y : ℕ) :
    (decompComplementLeft w x y).LO = (decomp w x y).N := by
  exact (decomp w x y).complementLeft_LO_eq_N

/-- In `(~x, y)`, the neither-active atom is the original `LO`. -/
@[simp] theorem decompComplementLeft_N_eq_LO (w x y : ℕ) :
    (decompComplementLeft w x y).N = (decomp w x y).LO := by
  exact (decomp w x y).complementLeft_N_eq_LO

/-- In `(x, ~y)`, the both-active atom is the original `LO`. -/
@[simp] theorem decompComplementRight_B_eq_LO (w x y : ℕ) :
    (decompComplementRight w x y).B = (decomp w x y).LO := by
  exact (decomp w x y).complementRight_B_eq_LO

/-- In `(x, ~y)`, the left-only atom is the original `B`. -/
@[simp] theorem decompComplementRight_LO_eq_B (w x y : ℕ) :
    (decompComplementRight w x y).LO = (decomp w x y).B := by
  exact (decomp w x y).complementRight_LO_eq_B

/-- In `(x, ~y)`, the right-only atom is the original `N`. -/
@[simp] theorem decompComplementRight_RO_eq_N (w x y : ℕ) :
    (decompComplementRight w x y).RO = (decomp w x y).N := by
  exact (decomp w x y).complementRight_RO_eq_N

/-- In `(x, ~y)`, the neither-active atom is the original `RO`. -/
@[simp] theorem decompComplementRight_N_eq_RO (w x y : ℕ) :
    (decompComplementRight w x y).N = (decomp w x y).RO := by
  exact (decomp w x y).complementRight_N_eq_RO

/-- In `(~x, ~y)`, the both-active atom is the original `N`. -/
@[simp] theorem decompComplementBoth_B_eq_N (w x y : ℕ) :
    (decompComplementBoth w x y).B = (decomp w x y).N := by
  exact (decomp w x y).complementBoth_B_eq_N

/-- In `(~x, ~y)`, the neither-active atom is the original `B`. -/
@[simp] theorem decompComplementBoth_N_eq_B (w x y : ℕ) :
    (decompComplementBoth w x y).N = (decomp w x y).B := by
  exact (decomp w x y).complementBoth_N_eq_B

/-- In `(~x, ~y)`, the left-only atom is the original `RO`. -/
@[simp] theorem decompComplementBoth_LO_eq_RO (w x y : ℕ) :
    (decompComplementBoth w x y).LO = (decomp w x y).RO := by
  exact (decomp w x y).complementBoth_LO_eq_RO

/-- In `(~x, ~y)`, the right-only atom is the original `LO`. -/
@[simp] theorem decompComplementBoth_RO_eq_LO (w x y : ℕ) :
    (decompComplementBoth w x y).RO = (decomp w x y).LO := by
  exact (decomp w x y).complementBoth_RO_eq_LO

end Bit
end BQD
end ABD
