import ABD.BQD.Bit.Additive.MaskedValue

namespace ABD
namespace BQD
namespace Bit
namespace Additive

/-- Entrance/completeness constructor for additive normal forms.

If ordinary natural numbers satisfy `x + y = c` and the output fits in the
common width, then the bit board built from `x` and `y` gives a genuine
`NormalForm`.  The heavy bit-evaluation work is isolated in
`boardOfPair_candidateC_eq_of_add_eq_of_c_lt`. -/
def ofAddEq (width x y c : ℕ)
    (hadd : x + y = c) (hc : c < 2 ^ width) :
    NormalForm width :=
  ofPair width x y c
    (boardOfPair_candidateC_eq_of_add_eq_of_c_lt hadd hc)
    hc

@[simp] theorem ofAddEq_board (width x y c : ℕ)
    (hadd : x + y = c) (hc : c < 2 ^ width) :
    (ofAddEq width x y c hadd hc).board = boardOfPair width x y := rfl

@[simp] theorem ofAddEq_c (width x y c : ℕ)
    (hadd : x + y = c) (hc : c < 2 ^ width) :
    (ofAddEq width x y c hadd hc).c = c := rfl

/-- The normal form generated from `x + y = c` recovers the left input. -/
@[simp] theorem ofAddEq_a (width x y c : ℕ)
    (hadd : x + y = c) (hc : c < 2 ^ width) :
    (ofAddEq width x y c hadd hc).a = x := by
  dsimp [ofAddEq, ofPair, ofBoard, NormalForm.a]
  exact boardOfPair_a_eq_left_of_add_eq_of_c_lt hadd hc

/-- The normal form generated from `x + y = c` recovers the right input. -/
@[simp] theorem ofAddEq_b (width x y c : ℕ)
    (hadd : x + y = c) (hc : c < 2 ^ width) :
    (ofAddEq width x y c hadd hc).b = y := by
  dsimp [ofAddEq, ofPair, ofBoard, NormalForm.b]
  exact boardOfPair_b_eq_right_of_add_eq_of_c_lt hadd hc

/-- The board candidate of the generated normal form is the actual output. -/
@[simp] theorem ofAddEq_candidateC_eq_c (width x y c : ℕ)
    (hadd : x + y = c) (hc : c < 2 ^ width) :
    (ofAddEq width x y c hadd hc).candidateC = c := by
  exact NormalForm.candidateC_eq_c (ofAddEq width x y c hadd hc)

/-- Soundness specialized to the entrance constructor. -/
@[simp] theorem ofAddEq_add_eq_c (width x y c : ℕ)
    (hadd : x + y = c) (hc : c < 2 ^ width) :
    (ofAddEq width x y c hadd hc).a +
      (ofAddEq width x y c hadd hc).b = c := by
  simpa using NormalForm.add_eq_c (ofAddEq width x y c hadd hc)

/-- The entrance constructor produces no-overflow normal forms. -/
theorem ofAddEq_noOverflow (width x y c : ℕ)
    (hadd : x + y = c) (hc : c < 2 ^ width) :
    ¬ (ofAddEq width x y c hadd hc).Overflow := by
  exact NormalForm.noOverflow (ofAddEq width x y c hadd hc)

end Additive
end Bit
end BQD
end ABD
