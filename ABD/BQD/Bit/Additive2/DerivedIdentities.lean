import ABD.BQD.Bit.Additive2.EvalLaws

namespace ABD
namespace BQD
namespace Bit
namespace Additive2

namespace NormalForm

variable {c : ℕ}

/-- Canonical complement value of the generated left integer: `RO + N`. -/
def notAValue (F : NormalForm c) : ℕ :=
  F.valRO + F.valN

/-- Canonical complement value of the generated right integer: `LO + N`. -/
def notBValue (F : NormalForm c) : ℕ :=
  F.valLO + F.valN

@[simp] theorem notAValue_def (F : NormalForm c) :
    F.notAValue = F.valRO + F.valN := rfl

@[simp] theorem notBValue_def (F : NormalForm c) :
    F.notBValue = F.valLO + F.valN := rfl

/-- The generated left value and its canonical complement fill the universe. -/
theorem a_add_notAValue_eq_universe (F : NormalForm c) :
    F.a + F.notAValue = evalMask F.U := by
  rw [← F.eval_cover]
  dsimp [NormalForm.a, notAValue, NormalForm.valB, NormalForm.valLO,
    NormalForm.valRO, NormalForm.valN, Board.a]
  ac_rfl

/-- The generated right value and its canonical complement fill the universe. -/
theorem b_add_notBValue_eq_universe (F : NormalForm c) :
    F.b + F.notBValue = evalMask F.U := by
  rw [← F.eval_cover]
  dsimp [NormalForm.b, notBValue, NormalForm.valB, NormalForm.valLO,
    NormalForm.valRO, NormalForm.valN, Board.b]
  ac_rfl

/-- The generated left value and its canonical complement fill `2^bitLength c - 1`. -/
@[simp] theorem a_add_notAValue_eq_pow_sub_one (F : NormalForm c) :
    F.a + F.notAValue = 2 ^ bitLength c - 1 := by
  rw [F.a_add_notAValue_eq_universe]
  exact F.eval_U

/-- The generated right value and its canonical complement fill `2^bitLength c - 1`. -/
@[simp] theorem b_add_notBValue_eq_pow_sub_one (F : NormalForm c) :
    F.b + F.notBValue = 2 ^ bitLength c - 1 := by
  rw [F.b_add_notBValue_eq_universe]
  exact F.eval_U

/-- The or-mask value plus the neither atom fills the universe. -/
theorem orValue_add_valN_eq_universe (F : NormalForm c) :
    F.orValue + F.valN = evalMask F.U := by
  rw [← F.eval_cover]
  dsimp [NormalForm.orValue, NormalForm.valN, NormalForm.valB, NormalForm.valLO,
    NormalForm.valRO, Board.orValue]

/-- The xor-mask value plus both common atoms fills the universe. -/
theorem xorValue_add_valB_add_valN_eq_universe (F : NormalForm c) :
    F.xorValue + F.valB + F.valN = evalMask F.U := by
  rw [← F.eval_cover]
  dsimp [NormalForm.xorValue, NormalForm.valB, NormalForm.valN,
    NormalForm.valLO, NormalForm.valRO, Board.xorValue]
  ac_rfl

/-- Safe Nat form of `c = U + B - N`: move `N` to the left. -/
theorem c_add_valN_eq_universe_add_valB (F : NormalForm c) :
    c + F.valN = evalMask F.U + F.valB := by
  have hCand :
      F.board.candidateC + F.valN = evalMask F.U + F.valB := by
    rw [← F.eval_cover]
    dsimp [Board.candidateC, Board.xorValue, Board.andValue,
      NormalForm.valB, NormalForm.valLO, NormalForm.valRO, NormalForm.valN]
    rw [Nat.two_mul]
    ac_rfl
  calc
    c + F.valN = F.board.candidateC + F.valN := by
      rw [F.hAdd]
    _ = evalMask F.U + F.valB := hCand


/-- Width-expanded form of the safe identity `c + N = U(c) + B`. -/
theorem c_add_valN_eq_pow_sub_one_add_valB (F : NormalForm c) :
    c + F.valN = (2 ^ bitLength c - 1) + F.valB := by
  rw [F.c_add_valN_eq_universe_add_valB]
  rw [F.eval_U]

/-- The two canonical complements add as xor plus twice the neither atom. -/
theorem notAValue_add_notBValue_eq_xorValue_add_two_mul_valN
    (F : NormalForm c) :
    F.notAValue + F.notBValue = F.xorValue + 2 * F.valN := by
  dsimp [notAValue, notBValue, NormalForm.xorValue]
  rw [Nat.two_mul]
  ac_rfl

end NormalForm
end Additive2
end Bit
end BQD
end ABD
