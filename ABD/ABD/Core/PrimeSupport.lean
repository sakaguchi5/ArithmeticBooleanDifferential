import Mathlib.Data.Nat.Factorization.Defs

namespace ABD

/-- The prime-support layer of a natural number, implemented by `Nat.factorization`.

For `n = 0`, this follows mathlib's convention for `Nat.factorization 0`.
The main intended use is for positive integers in later ABC-style statements.
-/
def supp (n : ℕ) : Finset ℕ :=
  n.factorization.support

/-- Alias spelling for the support layer. -/
def primeSupport (n : ℕ) : Finset ℕ :=
  supp n

@[simp]
theorem primeSupport_eq_supp (n : ℕ) :
    primeSupport n = supp n := by
  rfl

end ABD
