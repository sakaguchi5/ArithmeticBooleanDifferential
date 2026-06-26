import ABD.BQD.Calculus.AdditionLaws
import ABD.BQD.Bit.Decomp

namespace ABD
namespace BQD
namespace Bit

/-- Bit-level generate region for two natural numbers at common width `w`. -/
def bitGenerate (w x y : ℕ) : Finset ℕ :=
  (decomp w x y).Generate

/-- Bit-level propagate region for two natural numbers at common width `w`. -/
def bitPropagate (w x y : ℕ) : Finset ℕ :=
  (decomp w x y).Propagate

/-- Bit-level kill region for two natural numbers at common width `w`. -/
def bitKill (w x y : ℕ) : Finset ℕ :=
  (decomp w x y).Kill

/-- Sum bits before incoming carry at common width `w`. -/
def bitSumNoCarry (w x y : ℕ) : Finset ℕ :=
  (decomp w x y).SumNoCarry

@[simp] theorem bitGenerate_eq (w x y : ℕ) :
    bitGenerate w x y = (decomp w x y).K := rfl

@[simp] theorem bitPropagate_eq (w x y : ℕ) :
    bitPropagate w x y = (decomp w x y).exclusive := rfl

@[simp] theorem bitKill_eq (w x y : ℕ) :
    bitKill w x y = (decomp w x y).Z := rfl

@[simp] theorem bitSumNoCarry_eq_bitPropagate (w x y : ℕ) :
    bitSumNoCarry w x y = bitPropagate w x y := rfl

/-- Bit-level generate and propagate form the active region. -/
@[simp] theorem bitGenerate_union_bitPropagate_eq_active (w x y : ℕ) :
    bitGenerate w x y ∪ bitPropagate w x y = (decomp w x y).active := by
  exact (decomp w x y).Generate_union_Propagate_eq_active

/-- Bit-level generate, propagate, and kill split the common bit universe. -/
@[simp] theorem bitGenerate_union_bitPropagate_union_bitKill_eq_bitUniverse
    (w x y : ℕ) :
    bitGenerate w x y ∪ bitPropagate w x y ∪ bitKill w x y = bitUniverse w := by
  calc
    bitGenerate w x y ∪ bitPropagate w x y ∪ bitKill w x y
        = (decomp w x y).U := by
            exact (decomp w x y).Generate_union_Propagate_union_Kill_eq_U
    _ = bitUniverse w := rfl

/-- Bit-level propagate count is the Hamming distance between the two active
bit sets at width `w`. -/
theorem bitPropagate_card_eq_hammingDistance (w x y : ℕ) :
    (bitPropagate w x y).card = (decomp w x y).hammingDistance := by
  exact (decomp w x y).Propagate_card_eq_hammingDistance

end Bit
end BQD
end ABD
