/-
  ABD.ApparitionDepth.HenselQuotient

  Step 21E-3 of the Apparition-Depth Decomposition project.

  This file names the normalized error quotient in one finite Hensel step.
  Informally, when `omega^d - 1` is divisible by `p^r`, the quotient `q` is
  determined modulo `p` by

      omega^d = 1 + q * p^r    mod p^(r+1).
-/

import ABD.ApparitionDepth.HigherTermsVanish

namespace ApparitionDepth

/-! ## Normalized error quotient -/

/-- `q` is the normalized error quotient for the level-`r` root `omega`, read at
precision `p^(r+1)`:

`omega^d = 1 + q*p^r` in `ZMod (p^(r+1))`. -/
def FiniteHenselErrorQuotient (omega q p d r : Nat) : Prop :=
  (omega : ZMod (p ^ (r + 1))) ^ d =
    1 + (q : ZMod (p ^ (r + 1))) *
      (p ^ r : ZMod (p ^ (r + 1)))

/-- Existence of a normalized error quotient. -/
def FiniteHenselErrorQuotientExists (omega p d r : Nat) : Prop :=
  ∃ q : Nat, FiniteHenselErrorQuotient omega q p d r

/-- Constructor for a normalized error quotient. -/
theorem finiteHenselErrorQuotient_intro {omega q p d r : Nat}
    (h : (omega : ZMod (p ^ (r + 1))) ^ d =
      1 + (q : ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1)))) :
    FiniteHenselErrorQuotient omega q p d r :=
  h

/-- Projection from a normalized error quotient. -/
theorem finiteHenselErrorQuotient_eq {omega q p d r : Nat}
    (h : FiniteHenselErrorQuotient omega q p d r) :
    (omega : ZMod (p ^ (r + 1))) ^ d =
      1 + (q : ZMod (p ^ (r + 1))) *
        (p ^ r : ZMod (p ^ (r + 1))) :=
  h

/-- Constructor for quotient existence. -/
theorem finiteHenselErrorQuotientExists_intro {omega q p d r : Nat}
    (h : FiniteHenselErrorQuotient omega q p d r) :
    FiniteHenselErrorQuotientExists omega p d r :=
  ⟨q, h⟩

/-- Extract a quotient witness. -/
theorem finiteHenselErrorQuotientExists_witness {omega p d r : Nat}
    (h : FiniteHenselErrorQuotientExists omega p d r) :
    ∃ q : Nat, FiniteHenselErrorQuotient omega q p d r :=
  h

/-- The full local quotient package over an old level-`r` lift. -/
def FiniteHenselQuotientPackage (g omega p d j r : Nat) : Prop :=
  HenselBranchLiftAtLevel g omega p d j r →
    FiniteHenselErrorQuotientExists omega p d r

/-- Constructor for the quotient package. -/
theorem finiteHenselQuotientPackage_intro {g omega p d j r : Nat}
    (h : HenselBranchLiftAtLevel g omega p d j r →
      FiniteHenselErrorQuotientExists omega p d r) :
    FiniteHenselQuotientPackage g omega p d j r :=
  h

/-- Apply the quotient package. -/
theorem finiteHenselQuotientPackage_apply {g omega p d j r : Nat}
    (hquot : FiniteHenselQuotientPackage g omega p d j r)
    (hlift : HenselBranchLiftAtLevel g omega p d j r) :
    FiniteHenselErrorQuotientExists omega p d r :=
  hquot hlift

end ApparitionDepth
