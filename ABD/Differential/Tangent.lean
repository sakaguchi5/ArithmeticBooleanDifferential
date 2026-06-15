import ABD.Core.All

namespace ABD

/-- A tangent vector on a finite Boolean support `S`.

The value `x hp` should be read as the chosen value `D(p)` of a formal
arithmetic derivative on the prime direction `p ∈ S`.
-/
abbrev Tangent (S : Finset ℕ) : Type :=
  {p : ℕ // p ∈ S} → ℤ

/-- The zero tangent vector. -/
def zeroTangent (S : Finset ℕ) : Tangent S :=
  fun _ => 0

end ABD
