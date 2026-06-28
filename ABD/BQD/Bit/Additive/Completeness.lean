import ABD.BQD.Bit.Additive.MaskedValue

namespace ABD
namespace BQD
namespace Bit
namespace Additive

/-- Entrance/completeness constructor for canonical additive normal forms.

If ordinary natural numbers satisfy `x + y = c`, then the bit board built from
`x` and `y` at the canonical output width `bitLength c` gives a genuine
`NormalForm c`.

The heavy bit-evaluation work is isolated in
`boardOfPair_candidateC_eq_of_add_eq`. -/
def ofAddEq (x y c : ℕ) (hadd : x + y = c) :
    NormalForm c :=
  ofPair x y c (boardOfPair_candidateC_eq_of_add_eq hadd)

@[simp] theorem ofAddEq_board (x y c : ℕ) (hadd : x + y = c) :
    (ofAddEq x y c hadd).board = boardOfPair (bitLength c) x y := rfl

/-- The normal form generated from `x + y = c` recovers the left input. -/
@[simp] theorem ofAddEq_a (x y c : ℕ) (hadd : x + y = c) :
    (ofAddEq x y c hadd).a = x := by
  dsimp [ofAddEq, ofPair, ofBoard, NormalForm.a]
  exact boardOfPair_a_eq_left_of_add_eq hadd

/-- The normal form generated from `x + y = c` recovers the right input. -/
@[simp] theorem ofAddEq_b (x y c : ℕ) (hadd : x + y = c) :
    (ofAddEq x y c hadd).b = y := by
  dsimp [ofAddEq, ofPair, ofBoard, NormalForm.b]
  exact boardOfPair_b_eq_right_of_add_eq hadd

/-- The board candidate of the generated normal form is the actual output. -/
@[simp] theorem ofAddEq_candidateC_eq_c (x y c : ℕ) (hadd : x + y = c) :
    (ofAddEq x y c hadd).candidateC = c := by
  exact NormalForm.candidateC_eq_c (ofAddEq x y c hadd)

/-- Soundness specialized to the entrance constructor. -/
@[simp] theorem ofAddEq_add_eq_c (x y c : ℕ) (hadd : x + y = c) :
    (ofAddEq x y c hadd).a + (ofAddEq x y c hadd).b = c := by
  simpa using NormalForm.add_eq_c (ofAddEq x y c hadd)

/-- The entrance constructor produces canonical no-active-overflow normal forms. -/
theorem ofAddEq_noActiveOverflow (x y c : ℕ) (hadd : x + y = c) :
    (ofAddEq x y c hadd).board.active ⊆ (ofAddEq x y c hadd).U := by
  exact NormalForm.noActiveOverflow (ofAddEq x y c hadd)

end Additive
end Bit
end BQD
end ABD
