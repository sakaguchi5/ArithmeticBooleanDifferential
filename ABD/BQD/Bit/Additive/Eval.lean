import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ABD
namespace BQD
namespace Bit
namespace Additive

/-- Integer evaluation of a finite set of bit positions.

A set `S : Finset ℕ` is read as the bit mask whose `i`-th bit is one exactly
when `i ∈ S`.  The value is therefore `Σ i ∈ S, 2^i`. -/
def evalMask (S : Finset ℕ) : ℕ :=
  S.sum fun i => 2 ^ i

@[simp] theorem evalMask_empty :
    evalMask (∅ : Finset ℕ) = 0 := by
  simp [evalMask]

/-- Evaluation of a singleton bit position. -/
@[simp] theorem evalMask_singleton (i : ℕ) :
    evalMask ({i} : Finset ℕ) = 2 ^ i := by
  simp [evalMask]

end Additive
end Bit
end BQD
end ABD
