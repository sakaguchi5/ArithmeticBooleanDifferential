import Mathlib.Data.Nat.Log
import ABD.BQD.Bit.Width

namespace ABD
namespace BQD
namespace Bit
namespace Additive2

/-- Canonical output width used by additive normal forms.

For `c = 0` the width is `0`.  For positive `c`, this is the usual binary
length `⌊log₂ c⌋ + 1`.

This file intentionally keeps only the definition.  Theorems such as
`c < 2 ^ bitLength c` can be added later as the canonical-width API grows. -/
def bitLength (c : ℕ) : ℕ :=
  if c = 0 then 0 else Nat.log2 c + 1

/-- The canonical bit universe determined by an output `c`. -/
def outputUniverse (c : ℕ) : Finset ℕ :=
  bitUniverse (bitLength c)

/-- Integer value of the canonical all-ones universe determined by `c`. -/
def outputUniverseValue (c : ℕ) : ℕ :=
  2 ^ bitLength c - 1

end Additive2
end Bit
end BQD
end ABD
