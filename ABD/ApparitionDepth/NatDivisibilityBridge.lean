/-
  ABD.ApparitionDepth.NatDivisibilityBridge

  Step 8 of the Apparition-Depth Decomposition project.

  This file is the cautious bridge layer between:
    * Core Nat divisibility predicates (`DepthAtLeast`, `ExactDepth`), and
    * residue-ring predicates in `ZMod (p^r)` (`ResidueDepthAtLeast`,
      `ResidueExactDepth`).

  We deliberately keep the hard arithmetic equivalences as named bridge
  predicates first.  Later files can prove these predicates from the usual
  `ZMod` divisibility lemmas and side conditions.  This keeps the current layer
  robust while still allowing the moving-base side to transport information back
  to the Core side.
-/

import ABD.ApparitionDepth.MovingBase

namespace ApparitionDepth

/-- One-way bridge from residue depth to Nat divisibility depth.

Mathematically this is the direction

`((ell : ZMod (p^r))^d = 1) -> p^r ∣ ell^d - 1`.

It is kept as a predicate here; a later theorem layer can prove it from the
standard `ZMod` divisibility API. -/
def ResidueDepthToNat (ell p d r : Nat) : Prop :=
  ResidueDepthAtLeast ell p d r → DepthAtLeast ell p d r

/-- One-way bridge from Nat divisibility depth to residue depth.

Mathematically this is the direction

`p^r ∣ ell^d - 1 -> ((ell : ZMod (p^r))^d = 1)`. -/
def NatDepthToResidue (ell p d r : Nat) : Prop :=
  DepthAtLeast ell p d r → ResidueDepthAtLeast ell p d r

/-- Two-way agreement between the residue and Nat readings of depth at least
`r`. -/
def ResidueNatDepthAgree (ell p d r : Nat) : Prop :=
  ResidueDepthAtLeast ell p d r ↔ DepthAtLeast ell p d r

/-- Two-way agreement between exact residue depth and exact Nat depth. -/
def ResidueNatExactAgree (ell p d r : Nat) : Prop :=
  ResidueExactDepth ell p d r ↔ ExactDepth ell p d r

/-! ## Constructors and projections -/

theorem residueDepthToNat_intro {ell p d r : Nat}
    (h : ResidueDepthAtLeast ell p d r → DepthAtLeast ell p d r) :
    ResidueDepthToNat ell p d r :=
  h

theorem natDepthToResidue_intro {ell p d r : Nat}
    (h : DepthAtLeast ell p d r → ResidueDepthAtLeast ell p d r) :
    NatDepthToResidue ell p d r :=
  h

theorem residueNatDepthAgree_intro {ell p d r : Nat}
    (h₁ : ResidueDepthAtLeast ell p d r → DepthAtLeast ell p d r)
    (h₂ : DepthAtLeast ell p d r → ResidueDepthAtLeast ell p d r) :
    ResidueNatDepthAgree ell p d r :=
  ⟨h₁, h₂⟩

theorem residueNatExactAgree_intro {ell p d r : Nat}
    (h₁ : ResidueExactDepth ell p d r → ExactDepth ell p d r)
    (h₂ : ExactDepth ell p d r → ResidueExactDepth ell p d r) :
    ResidueNatExactAgree ell p d r :=
  ⟨h₁, h₂⟩

theorem residueDepthToNat_apply {ell p d r : Nat}
    (hbridge : ResidueDepthToNat ell p d r)
    (hres : ResidueDepthAtLeast ell p d r) :
    DepthAtLeast ell p d r :=
  hbridge hres

theorem natDepthToResidue_apply {ell p d r : Nat}
    (hbridge : NatDepthToResidue ell p d r)
    (hdepth : DepthAtLeast ell p d r) :
    ResidueDepthAtLeast ell p d r :=
  hbridge hdepth

theorem residueNatDepthAgree_toNat {ell p d r : Nat}
    (hbridge : ResidueNatDepthAgree ell p d r) :
    ResidueDepthToNat ell p d r :=
  hbridge.mp

theorem residueNatDepthAgree_toResidue {ell p d r : Nat}
    (hbridge : ResidueNatDepthAgree ell p d r) :
    NatDepthToResidue ell p d r :=
  hbridge.mpr

theorem residueNatExactAgree_toNat {ell p d r : Nat}
    (hbridge : ResidueNatExactAgree ell p d r)
    (hexact : ResidueExactDepth ell p d r) :
    ExactDepth ell p d r :=
  hbridge.mp hexact

theorem residueNatExactAgree_toResidue {ell p d r : Nat}
    (hbridge : ResidueNatExactAgree ell p d r)
    (hexact : ExactDepth ell p d r) :
    ResidueExactDepth ell p d r :=
  hbridge.mpr hexact

/-! ## Moving-base transport back to Core -/

/-- A moving-base class gives Core depth at least `r`, once the residue-to-Nat
bridge is available for `ell`. -/
theorem depthAtLeast_of_movingBaseClass_of_residueDepthToNat
    {ell omega p d r : Nat}
    (hmb : MovingBaseClass ell omega p d r)
    (hbridge : ResidueDepthToNat ell p d r) :
    DepthAtLeast ell p d r :=
  hbridge (movingBaseClass_residueDepthAtLeast hmb)

/-- Exact moving-base certificates also give the positive Core depth part at
level `r`, once the residue-to-Nat bridge is available.  The negative `r+1`
part intentionally remains separate, as in `MovingBase`. -/
theorem depthAtLeast_of_movingBaseExactClass_of_residueDepthToNat
    {ell omega p d r : Nat}
    (hmb : MovingBaseExactClass ell omega p d r)
    (hbridge : ResidueDepthToNat ell p d r) :
    DepthAtLeast ell p d r :=
  hbridge (movingBaseExactClass_residueDepthAtLeast hmb)

/-- If exact residue depth is known directly for `ell`, exact Core depth follows
from exact agreement. -/
theorem exactDepth_of_residueExactDepth_of_agree {ell p d r : Nat}
    (hbridge : ResidueNatExactAgree ell p d r)
    (hres : ResidueExactDepth ell p d r) :
    ExactDepth ell p d r :=
  hbridge.mp hres

/-- If exact Core depth is known, exact residue depth follows from exact
agreement. -/
theorem residueExactDepth_of_exactDepth_of_agree {ell p d r : Nat}
    (hbridge : ResidueNatExactAgree ell p d r)
    (hexact : ExactDepth ell p d r) :
    ResidueExactDepth ell p d r :=
  hbridge.mpr hexact

end ApparitionDepth
