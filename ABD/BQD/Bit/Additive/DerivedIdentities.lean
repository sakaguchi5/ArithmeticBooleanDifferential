import ABD.BQD.Bit.Additive.EvalLaws

namespace ABD
namespace BQD
namespace Bit
namespace Additive

namespace Board

variable {width : ℕ}

/-- Fixed-width complement value of the generated left integer: `RO + N`. -/
def notAValue (G : Board width) : ℕ :=
  G.valRO + G.valN

/-- Fixed-width complement value of the generated right integer: `LO + N`. -/
def notBValue (G : Board width) : ℕ :=
  G.valLO + G.valN

@[simp] theorem notAValue_def (G : Board width) :
    G.notAValue = G.valRO + G.valN := rfl

@[simp] theorem notBValue_def (G : Board width) :
    G.notBValue = G.valLO + G.valN := rfl

/-- The generated left value and its fixed-width complement fill the universe. -/
theorem a_add_notAValue_eq_universe (G : Board width) :
    G.a + G.notAValue = evalMask (bitUniverse width) := by
  rw [← G.eval_cover]
  dsimp [Board.a, notAValue]
  ac_rfl

/-- The generated right value and its fixed-width complement fill the universe. -/
theorem b_add_notBValue_eq_universe (G : Board width) :
    G.b + G.notBValue = evalMask (bitUniverse width) := by
  rw [← G.eval_cover]
  dsimp [Board.b, notBValue]
  ac_rfl

/-- The generated left value and its fixed-width complement fill `2^width - 1`. -/
@[simp] theorem a_add_notAValue_eq_pow_sub_one (G : Board width) :
    G.a + G.notAValue = 2 ^ width - 1 := by
  rw [G.a_add_notAValue_eq_universe]
  exact evalMask_bitUniverse width

/-- The generated right value and its fixed-width complement fill `2^width - 1`. -/
@[simp] theorem b_add_notBValue_eq_pow_sub_one (G : Board width) :
    G.b + G.notBValue = 2 ^ width - 1 := by
  rw [G.b_add_notBValue_eq_universe]
  exact evalMask_bitUniverse width

/-- The or-mask value plus the neither atom fills the universe. -/
theorem orValue_add_valN_eq_universe (G : Board width) :
    G.orValue + G.valN = evalMask (bitUniverse width) := by
  rw [← G.eval_cover]
  dsimp [Board.orValue]

/-- The xor-mask value plus both common atoms fills the universe. -/
theorem xorValue_add_valB_add_valN_eq_universe (G : Board width) :
    G.xorValue + G.valB + G.valN = evalMask (bitUniverse width) := by
  rw [← G.eval_cover]
  dsimp [Board.xorValue]
  ac_rfl

/-- Safe Nat form of `candidateC = U + B - N`: move `N` to the left. -/
theorem candidateC_add_valN_eq_universe_add_valB (G : Board width) :
    G.candidateC + G.valN = evalMask (bitUniverse width) + G.valB := by
  rw [← G.eval_cover]
  dsimp [Board.candidateC, Board.xorValue, Board.andValue]
  rw [two_mul]
  ac_rfl

/-- Width-expanded form of the safe identity `candidateC + N = U + B`. -/
theorem candidateC_add_valN_eq_pow_sub_one_add_valB (G : Board width) :
    G.candidateC + G.valN = (2 ^ width - 1) + G.valB := by
  rw [G.candidateC_add_valN_eq_universe_add_valB]
  rw [evalMask_bitUniverse]

/-- The two fixed-width complements add as xor plus twice the neither atom. -/
theorem notAValue_add_notBValue_eq_xorValue_add_two_mul_valN
    (G : Board width) :
    G.notAValue + G.notBValue = G.xorValue + 2 * G.valN := by
  dsimp [notAValue, notBValue, Board.xorValue]
  rw [two_mul]
  ac_rfl

end Board

namespace NormalForm

variable {width : ℕ}

/-- Fixed-width complement value of the generated left integer. -/
def notAValue (F : NormalForm width) : ℕ :=
  F.board.notAValue

/-- Fixed-width complement value of the generated right integer. -/
def notBValue (F : NormalForm width) : ℕ :=
  F.board.notBValue

@[simp] theorem notAValue_def (F : NormalForm width) :
    F.notAValue = F.board.notAValue := rfl

@[simp] theorem notBValue_def (F : NormalForm width) :
    F.notBValue = F.board.notBValue := rfl

/-- The generated left value and its fixed-width complement fill the universe. -/
theorem a_add_notAValue_eq_universe (F : NormalForm width) :
    F.a + F.notAValue = evalMask (bitUniverse width) := by
  simpa [NormalForm.a, notAValue] using F.board.a_add_notAValue_eq_universe

/-- The generated right value and its fixed-width complement fill the universe. -/
theorem b_add_notBValue_eq_universe (F : NormalForm width) :
    F.b + F.notBValue = evalMask (bitUniverse width) := by
  simpa [NormalForm.b, notBValue] using F.board.b_add_notBValue_eq_universe

/-- The generated left value and its fixed-width complement fill `2^width - 1`. -/
@[simp] theorem a_add_notAValue_eq_pow_sub_one (F : NormalForm width) :
    F.a + F.notAValue = 2 ^ width - 1 := by
  rw [F.a_add_notAValue_eq_universe]
  exact evalMask_bitUniverse width

/-- The generated right value and its fixed-width complement fill `2^width - 1`. -/
@[simp] theorem b_add_notBValue_eq_pow_sub_one (F : NormalForm width) :
    F.b + F.notBValue = 2 ^ width - 1 := by
  rw [F.b_add_notBValue_eq_universe]
  exact evalMask_bitUniverse width

/-- The or-mask value plus the neither atom fills the universe. -/
theorem orValue_add_valN_eq_universe (F : NormalForm width) :
    F.orValue + F.valN = evalMask (bitUniverse width) := by
  simpa [NormalForm.orValue, NormalForm.valN] using F.board.orValue_add_valN_eq_universe

/-- The xor-mask value plus both common atoms fills the universe. -/
theorem xorValue_add_valB_add_valN_eq_universe (F : NormalForm width) :
    F.xorValue + F.valB + F.valN = evalMask (bitUniverse width) := by
  simpa [NormalForm.xorValue, NormalForm.valB, NormalForm.valN]
    using F.board.xorValue_add_valB_add_valN_eq_universe

/-- Safe Nat form of `c = U + B - N`: move `N` to the left. -/
theorem c_add_valN_eq_universe_add_valB (F : NormalForm width) :
    F.c + F.valN = evalMask (bitUniverse width) + F.valB := by
  rw [← F.hAdd]
  simpa [NormalForm.candidateC, NormalForm.valN, NormalForm.valB]
    using F.board.candidateC_add_valN_eq_universe_add_valB

/-- Width-expanded form of the safe identity `c + N = U + B`. -/
theorem c_add_valN_eq_pow_sub_one_add_valB (F : NormalForm width) :
    F.c + F.valN = (2 ^ width - 1) + F.valB := by
  rw [F.c_add_valN_eq_universe_add_valB]
  rw [evalMask_bitUniverse]

/-- The two fixed-width complements add as xor plus twice the neither atom. -/
theorem notAValue_add_notBValue_eq_xorValue_add_two_mul_valN
    (F : NormalForm width) :
    F.notAValue + F.notBValue = F.xorValue + 2 * F.valN := by
  simpa [notAValue, notBValue, NormalForm.xorValue, NormalForm.valN]
    using F.board.notAValue_add_notBValue_eq_xorValue_add_two_mul_valN

end NormalForm
end Additive
end Bit
end BQD
end ABD
