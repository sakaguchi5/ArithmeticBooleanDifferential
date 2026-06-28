import Mathlib.Data.Nat.Log
import ABD.BQD.Bit.Width

namespace ABD
namespace BQD
namespace Bit
namespace Additive

/-- Canonical output width used by additive normal forms.

For `c = 0` the width is `0`.  For positive `c`, this is the usual binary
length `⌊log₂ c⌋ + 1`.

This file also isolates the canonical-width bound as a small API point.
-/
def bitLength (c : ℕ) : ℕ :=
  if c = 0 then 0 else Nat.log2 c + 1

--cが常に正ならこっちでいいかも
def width (c : ℕ) : ℕ :=
  Nat.log2 c + 1

/-- The canonical bit universe determined by an output `c`. -/
def outputUniverse (c : ℕ) : Finset ℕ :=
  bitUniverse (bitLength c)

/-- Integer value of the canonical all-ones universe determined by `c`. -/
def outputUniverseValue (c : ℕ) : ℕ :=
  2 ^ bitLength c - 1

/-- Canonical output bound for the chosen `bitLength`.

This is the standard log₂ fact `c < 2 ^ bitLength c`.  It is isolated here so
that the additive completeness layer can be stated without carrying an external
fixed-width bound. -/
theorem lt_two_pow_bitLength (c : ℕ) :
    c < 2 ^ bitLength c := by
  by_cases h : c = 0
  · subst c
    simp [bitLength]
  · unfold bitLength
    simp [h]
    simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one]
      using Nat.lt_pow_succ_log_self (by decide : 1 < 2) c

end Additive
end Bit
end BQD
end ABD
