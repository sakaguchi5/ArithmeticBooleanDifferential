/-
  ABD.ApparitionDepth2.Basic

  New public-facing Apparition-Depth layer.

  This folder is intentionally not a line-by-line refactor of the archived
  `ABD.ApparitionDepth` development.  The old folder is treated as a checked
  archive.  This folder exposes the same mathematical objects in a more organic
  order.

  Public objects in this file:
    * N
    * AppearsAt
    * FirstAppearsAt
    * DepthAtLeast
    * ExactDepth
    * FirstAppearsWithDepthAtLeast
    * FirstAppearsWithExactDepth
-/

import ABD.ApparitionDepth.CoreBasic

namespace ApparitionDepth2

/-- The basic sequence `ell^n - 1`. -/
abbrev N (ell n : Nat) : Nat :=
  ApparitionDepth.N ell n

/-- `p` appears at exponent `n` for the base `ell`. -/
abbrev AppearsAt (ell p n : Nat) : Prop :=
  ApparitionDepth.AppearsAt ell p n

/-- `p` first appears at exponent `d` for the base `ell`. -/
abbrev FirstAppearsAt (ell p d : Nat) : Prop :=
  ApparitionDepth.FirstAppearsAt ell p d

/-- The initial depth at exponent `d` is at least `r`. -/
abbrev DepthAtLeast (ell p d r : Nat) : Prop :=
  ApparitionDepth.DepthAtLeast ell p d r

/-- The initial depth at exponent `d` is exactly `r`. -/
abbrev ExactDepth (ell p d r : Nat) : Prop :=
  ApparitionDepth.ExactDepth ell p d r

/-- `p` first appears at `d`, and its initial depth is at least `r`. -/
abbrev FirstAppearsWithDepthAtLeast (ell p d r : Nat) : Prop :=
  ApparitionDepth.FirstAppearsWithDepthAtLeast ell p d r

/-- `p` first appears at `d`, and its initial depth is exactly `r`. -/
abbrev FirstAppearsWithExactDepth (ell p d r : Nat) : Prop :=
  ApparitionDepth.FirstAppearsWithExactDepth ell p d r

/-! ## Public constructors and projections -/

theorem firstAppearsAt_intro {ell p d : Nat}
    (hd_pos : 0 < d)
    (hd_app : AppearsAt ell p d)
    (hmin : ∀ m : Nat, 0 < m → m < d → ¬ AppearsAt ell p m) :
    FirstAppearsAt ell p d :=
  ApparitionDepth.firstAppearsAt_intro hd_pos hd_app hmin

theorem firstAppears_pos {ell p d : Nat}
    (h : FirstAppearsAt ell p d) : 0 < d :=
  ApparitionDepth.firstAppears_pos h

theorem firstAppears_appears {ell p d : Nat}
    (h : FirstAppearsAt ell p d) : AppearsAt ell p d :=
  ApparitionDepth.firstAppears_appears h

theorem firstAppears_not_before {ell p d m : Nat}
    (h : FirstAppearsAt ell p d)
    (hm_pos : 0 < m)
    (hm_lt : m < d) :
    ¬ AppearsAt ell p m :=
  ApparitionDepth.firstAppears_not_before h hm_pos hm_lt

theorem depthAtLeast_zero (ell p d : Nat) :
    DepthAtLeast ell p d 0 :=
  ApparitionDepth.depthAtLeast_zero ell p d

theorem depthAtLeast_one_iff {ell p d : Nat} :
    DepthAtLeast ell p d 1 ↔ AppearsAt ell p d :=
  ApparitionDepth.depthAtLeast_one_iff

theorem firstWithDepth_intro {ell p d r : Nat}
    (hfirst : FirstAppearsAt ell p d)
    (hdepth : DepthAtLeast ell p d r) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  ApparitionDepth.firstWithDepth_intro hfirst hdepth

theorem firstWithDepth_first {ell p d r : Nat}
    (h : FirstAppearsWithDepthAtLeast ell p d r) :
    FirstAppearsAt ell p d :=
  ApparitionDepth.firstWithDepth_first h

theorem firstWithDepth_depth {ell p d r : Nat}
    (h : FirstAppearsWithDepthAtLeast ell p d r) :
    DepthAtLeast ell p d r :=
  ApparitionDepth.firstWithDepth_depth h

end ApparitionDepth2
