/-
  ABD.ApparitionDepth3.Basic

  Independent Apparition-Depth core.
  This file does not import the archived ApparitionDepth or ApparitionDepth2
  folders.  It keeps only the elementary arithmetic predicates.
-/

namespace ApparitionDepth3

/-- The basic sequence attached to a base `ell`: `ell^n - 1`. -/
def N (ell n : Nat) : Nat :=
  ell ^ n - 1

/-- `p` appears at exponent `n` for the base `ell`. -/
def AppearsAt (ell p n : Nat) : Prop :=
  p ∣ N ell n

/-- `p` first appears at exponent `d` for the base `ell`. -/
def FirstAppearsAt (ell p d : Nat) : Prop :=
  0 < d ∧ AppearsAt ell p d ∧
    ∀ m : Nat, 0 < m → m < d → ¬ AppearsAt ell p m

/-- The depth at exponent `d` is at least `r`. -/
def DepthAtLeast (ell p d r : Nat) : Prop :=
  p ^ r ∣ N ell d

/-- The depth at exponent `d` is exactly `r`. -/
def ExactDepth (ell p d r : Nat) : Prop :=
  DepthAtLeast ell p d r ∧ ¬ DepthAtLeast ell p d (r + 1)

/-- First apparition together with a lower bound on initial depth. -/
def FirstAppearsWithDepthAtLeast (ell p d r : Nat) : Prop :=
  FirstAppearsAt ell p d ∧ DepthAtLeast ell p d r

/-- First apparition together with exact initial depth. -/
def FirstAppearsWithExactDepth (ell p d r : Nat) : Prop :=
  FirstAppearsAt ell p d ∧ ExactDepth ell p d r

/-! ## Core constructors and projections -/

theorem firstAppearsAt_intro {ell p d : Nat}
    (hd_pos : 0 < d)
    (hd_app : AppearsAt ell p d)
    (hmin : ∀ m : Nat, 0 < m → m < d → ¬ AppearsAt ell p m) :
    FirstAppearsAt ell p d :=
  ⟨hd_pos, hd_app, hmin⟩

theorem firstAppears_pos {ell p d : Nat}
    (h : FirstAppearsAt ell p d) : 0 < d :=
  h.1

theorem firstAppears_appears {ell p d : Nat}
    (h : FirstAppearsAt ell p d) : AppearsAt ell p d :=
  h.2.1

theorem firstAppears_not_before {ell p d m : Nat}
    (h : FirstAppearsAt ell p d)
    (hm_pos : 0 < m)
    (hm_lt : m < d) :
    ¬ AppearsAt ell p m :=
  h.2.2 m hm_pos hm_lt

theorem exactDepth_intro {ell p d r : Nat}
    (hdepth : DepthAtLeast ell p d r)
    (hnot : ¬ DepthAtLeast ell p d (r + 1)) :
    ExactDepth ell p d r :=
  ⟨hdepth, hnot⟩

theorem exactDepth_depthAtLeast {ell p d r : Nat}
    (h : ExactDepth ell p d r) : DepthAtLeast ell p d r :=
  h.1

theorem exactDepth_not_next {ell p d r : Nat}
    (h : ExactDepth ell p d r) : ¬ DepthAtLeast ell p d (r + 1) :=
  h.2

theorem firstWithDepth_intro {ell p d r : Nat}
    (hfirst : FirstAppearsAt ell p d)
    (hdepth : DepthAtLeast ell p d r) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  ⟨hfirst, hdepth⟩

theorem firstWithDepth_first {ell p d r : Nat}
    (h : FirstAppearsWithDepthAtLeast ell p d r) : FirstAppearsAt ell p d :=
  h.1

theorem firstWithDepth_depth {ell p d r : Nat}
    (h : FirstAppearsWithDepthAtLeast ell p d r) : DepthAtLeast ell p d r :=
  h.2

/-- Depth at least zero is automatic. -/
theorem depthAtLeast_zero (ell p d : Nat) :
    DepthAtLeast ell p d 0 := by
  unfold DepthAtLeast
  simp

/-- Depth at least one is ordinary appearance. -/
theorem depthAtLeast_one_iff {ell p d : Nat} :
    DepthAtLeast ell p d 1 ↔ AppearsAt ell p d := by
  unfold DepthAtLeast AppearsAt
  simp

end ApparitionDepth3
