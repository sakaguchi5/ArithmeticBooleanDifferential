import ABD.BQD.Bit.Additive.EvalLaws

namespace ABD
namespace BQD
namespace Bit
namespace Additive
namespace NormalForm

variable {width : ℕ}

/-- Fixed-width complement value of the generated left integer: `RO + N`. -/
def notAValue (F : NormalForm width) : ℕ :=
  F.valRO + F.valN

/-- Fixed-width complement value of the generated right integer: `LO + N`. -/
def notBValue (F : NormalForm width) : ℕ :=
  F.valLO + F.valN

@[simp] theorem notAValue_def (F : NormalForm width) :
    F.notAValue = F.valRO + F.valN := rfl

@[simp] theorem notBValue_def (F : NormalForm width) :
    F.notBValue = F.valLO + F.valN := rfl

/-- The generated left value and its fixed-width complement fill the universe. -/
theorem a_add_notAValue_eq_universe (F : NormalForm width) :
    F.a + F.notAValue = evalMask (bitUniverse width) := by
  rw [← F.eval_cover]
  dsimp [a, notAValue]
  ac_rfl

/-- The generated right value and its fixed-width complement fill the universe. -/
theorem b_add_notBValue_eq_universe (F : NormalForm width) :
    F.b + F.notBValue = evalMask (bitUniverse width) := by
  rw [← F.eval_cover]
  dsimp [b, notBValue]
  ac_rfl

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
  rw [← F.eval_cover]
  dsimp [orValue]

/-- The xor-mask value plus both common atoms fills the universe. -/
theorem xorValue_add_valB_add_valN_eq_universe (F : NormalForm width) :
    F.xorValue + F.valB + F.valN = evalMask (bitUniverse width) := by
  rw [← F.eval_cover]
  dsimp [xorValue]
  ac_rfl

/-- Safe Nat form of `c = U + B - N`: move `N` to the left. -/
theorem c_add_valN_eq_universe_add_valB (F : NormalForm width) :
    F.c + F.valN = evalMask (bitUniverse width) + F.valB := by
  rw [← F.eval_cover]
  dsimp [c]
  rw [two_mul]
  ac_rfl

/-- Width-expanded form of the safe identity `c + N = U + B`. -/
theorem c_add_valN_eq_pow_sub_one_add_valB (F : NormalForm width) :
    F.c + F.valN = (2 ^ width - 1) + F.valB := by
  rw [F.c_add_valN_eq_universe_add_valB]
  rw [evalMask_bitUniverse]

/-- The two fixed-width complements add as xor plus twice the neither atom. -/
theorem notAValue_add_notBValue_eq_xorValue_add_two_mul_valN
    (F : NormalForm width) :
    F.notAValue + F.notBValue = F.xorValue + 2 * F.valN := by
  dsimp [notAValue, notBValue, xorValue]
  rw [two_mul]
  ac_rfl

end NormalForm
end Additive
end Bit
end BQD
end ABD
