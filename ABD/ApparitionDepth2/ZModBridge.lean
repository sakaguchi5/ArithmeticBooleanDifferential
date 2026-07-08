/-
  ABD.ApparitionDepth2.ZModBridge

  Standard bridge between the finite residue-ring language and the core
  divisibility-depth language.

  Public theorem theme:
    depth >= r  <->  root at level p^r.
-/

import ABD.ApparitionDepth.ResidueDepthBridgeProof
import ABD.ApparitionDepth2.Basic

namespace ApparitionDepth2

/-- `x` is a `d`-th root of unity modulo `p^r`. -/
abbrev RootAtLevel (x p d r : Nat) : Prop :=
  ApparitionDepth.ResidueDepthAtLeast x p d r

/-- Exact root-level statement: root at `r`, but not at `r+1`. -/
abbrev ExactRootAtLevel (x p d r : Nat) : Prop :=
  ApparitionDepth.ResidueExactDepth x p d r

/-- The canonical bridge: root at level `p^r` iff depth is at least `r`. -/
theorem rootAtLevel_iff_depthAtLeast_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell) :
    RootAtLevel ell p d r ↔ DepthAtLeast ell p d r :=
  ApparitionDepth.residueDepthAtLeast_iff_depthAtLeast_of_base_pos hell_pos

/-- Forward direction of the canonical bridge. -/
theorem depthAtLeast_of_rootAtLevel_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell)
    (hroot : RootAtLevel ell p d r) :
    DepthAtLeast ell p d r :=
  ApparitionDepth.depthAtLeast_of_residueDepthAtLeast_of_base_pos hell_pos hroot

/-- Reverse direction of the canonical bridge. -/
theorem rootAtLevel_of_depthAtLeast_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell)
    (hdepth : DepthAtLeast ell p d r) :
    RootAtLevel ell p d r :=
  ApparitionDepth.residueDepthAtLeast_of_depthAtLeast_of_base_pos hell_pos hdepth

/-- Exact-depth version of the residue/Core bridge. -/
theorem exactRootAtLevel_iff_exactDepth_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell) :
    ExactRootAtLevel ell p d r ↔ ExactDepth ell p d r :=
  ApparitionDepth.residueNatExactAgree_of_base_pos hell_pos

end ApparitionDepth2
