/-
  ABD.ApparitionDepth.ResidueDepthBridgeProof

  Step 11 of the Apparition-Depth Decomposition project.

  This file proves the actual bridge

      ResidueDepthAtLeast ell p d r  <->  DepthAtLeast ell p d r

  under the natural side condition `0 < ell`.  This is the `p^r` analogue of
  `UnitAppearsBridgeProof`: the residue-ring statement in `ZMod (p^r)` is
  identified with the Core Nat divisibility statement.

  The condition `0 < ell` is mathematically harmless for the intended use,
  where `ell` is a base prime.  It is useful because Core defines

      N ell d = ell^d - 1

  using natural subtraction, so rewriting modular equality as divisibility of
  `ell^d - 1` needs `1 <= ell^d`.
-/

import ABD.ApparitionDepth.UnitAppearsBridgeProof
import Mathlib.Data.Nat.ModEq

namespace ApparitionDepth

/-! ## Residue depth is ordinary Nat divisibility depth -/

/-- Residue depth modulo `p^r` is equivalent to Core divisibility depth.

This proves the arithmetic bridge that was previously isolated as a placeholder:

`((ell : ZMod (p^r))^d = 1) <-> p^r ∣ ell^d - 1`.

The proof is the same modular-equality-to-divisibility argument used in
`UnitAppearsBridgeProof`, with modulus `p^r` instead of `p`. -/
theorem residueDepthAtLeast_iff_depthAtLeast_of_pow_pos {ell p d r : Nat}
    (hpos : 0 < ell ^ d) :
    ResidueDepthAtLeast ell p d r ↔ DepthAtLeast ell p d r := by
  unfold ResidueDepthAtLeast DepthAtLeast N
  rw [← Nat.cast_pow]
  rw [← Nat.cast_one]
  rw [ZMod.natCast_eq_natCast_iff (ell ^ d) 1 (p ^ r)]
  simpa [Nat.ModEq.comm] using
    (Nat.modEq_iff_dvd' (n := p ^ r) (a := 1) (b := ell ^ d) hpos)

/-- The same bridge in the intended base-positive form. -/
theorem residueDepthAtLeast_iff_depthAtLeast_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell) :
    ResidueDepthAtLeast ell p d r ↔ DepthAtLeast ell p d r :=
  residueDepthAtLeast_iff_depthAtLeast_of_pow_pos (Nat.pow_pos hell_pos)

/-- Forward direction: a residue-depth certificate gives Core depth. -/
theorem depthAtLeast_of_residueDepthAtLeast_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell)
    (hres : ResidueDepthAtLeast ell p d r) :
    DepthAtLeast ell p d r :=
  (residueDepthAtLeast_iff_depthAtLeast_of_base_pos
    (ell := ell) (p := p) (d := d) (r := r) hell_pos).mp hres

/-- Reverse direction: Core depth gives residue-depth. -/
theorem residueDepthAtLeast_of_depthAtLeast_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell)
    (hdepth : DepthAtLeast ell p d r) :
    ResidueDepthAtLeast ell p d r :=
  (residueDepthAtLeast_iff_depthAtLeast_of_base_pos
    (ell := ell) (p := p) (d := d) (r := r) hell_pos).mpr hdepth

/-! ## Filling the named bridge predicates from `NatDivisibilityBridge` -/

/-- The residue-to-Nat bridge is available for positive bases. -/
theorem residueDepthToNat_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell) :
    ResidueDepthToNat ell p d r :=
  fun hres => depthAtLeast_of_residueDepthAtLeast_of_base_pos hell_pos hres

/-- The Nat-to-residue bridge is available for positive bases. -/
theorem natDepthToResidue_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell) :
    NatDepthToResidue ell p d r :=
  fun hdepth => residueDepthAtLeast_of_depthAtLeast_of_base_pos hell_pos hdepth

/-- Full agreement between residue depth and Core depth for positive bases. -/
theorem residueNatDepthAgree_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell) :
    ResidueNatDepthAgree ell p d r :=
  residueDepthAtLeast_iff_depthAtLeast_of_base_pos hell_pos

/-- Exact residue depth agrees with exact Core depth for positive bases. -/
theorem residueNatExactAgree_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell) :
    ResidueNatExactAgree ell p d r := by
  unfold ResidueNatExactAgree ResidueExactDepth ExactDepth
  constructor
  · intro hresExact
    refine ⟨?_, ?_⟩
    · exact depthAtLeast_of_residueDepthAtLeast_of_base_pos hell_pos hresExact.1
    · intro hnext
      exact hresExact.2
        (residueDepthAtLeast_of_depthAtLeast_of_base_pos
          (ell := ell) (p := p) (d := d) (r := r + 1) hell_pos hnext)
  · intro hexact
    refine ⟨?_, ?_⟩
    · exact residueDepthAtLeast_of_depthAtLeast_of_base_pos hell_pos hexact.1
    · intro hresNext
      exact hexact.2
        (depthAtLeast_of_residueDepthAtLeast_of_base_pos
          (ell := ell) (p := p) (d := d) (r := r + 1) hell_pos hresNext)

/-! ## Moving-base transport back to Core, now without placeholder bridge input -/

/-- A moving-base class gives Core depth at least `r` for positive bases. -/
theorem depthAtLeast_of_movingBaseClass_of_base_pos
    {ell omega p d r : Nat}
    (hmb : MovingBaseClass ell omega p d r)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  depthAtLeast_of_residueDepthAtLeast_of_base_pos hell_pos
    (movingBaseClass_residueDepthAtLeast hmb)

/-- Exact moving-base certificates also give the positive Core depth part at
level `r` for positive bases.  As before, the negative `r+1` part is not
transported from `omega` to `ell` without a stronger congruence modulo
`p^(r+1)`. -/
theorem depthAtLeast_of_movingBaseExactClass_of_base_pos
    {ell omega p d r : Nat}
    (hmb : MovingBaseExactClass ell omega p d r)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  depthAtLeast_of_residueDepthAtLeast_of_base_pos hell_pos
    (movingBaseExactClass_residueDepthAtLeast hmb)

/-- Direct exact-depth transport for a residue-exact statement about the same
base `ell`. -/
theorem exactDepth_of_residueExactDepth_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell)
    (hresExact : ResidueExactDepth ell p d r) :
    ExactDepth ell p d r :=
  (residueNatExactAgree_of_base_pos
    (ell := ell) (p := p) (d := d) (r := r) hell_pos).mp hresExact

/-- Direct reverse exact-depth transport for the same base `ell`. -/
theorem residueExactDepth_of_exactDepth_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell)
    (hexact : ExactDepth ell p d r) :
    ResidueExactDepth ell p d r :=
  (residueNatExactAgree_of_base_pos
    (ell := ell) (p := p) (d := d) (r := r) hell_pos).mpr hexact

end ApparitionDepth
