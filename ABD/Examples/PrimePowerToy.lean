import ABD.Differential.All

namespace ABD.Examples

/-- A toy Boolean support for a prime-power-shaped equation such as
`p^m + q^n = r^k`.

No primality assumptions are imposed yet; this is only the finite support carrier.
-/
def primePowerSupport (p q r : ℕ) : Finset ℕ :=
  {p, q, r}

/-- The zero tangent is always additive on any selected equation. -/
example (p q r a b c : ℕ) :
    ABD.AdditiveOn (primePowerSupport p q r)
      (ABD.zeroTangent (primePowerSupport p q r)) a b c := by
  simp

end ABD.Examples
