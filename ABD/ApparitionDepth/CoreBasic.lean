/-
  ABD.ApparitionDepth.CoreBasic

  Step 2a of the Apparition-Depth Decomposition project.

  This file stays deliberately close to `Core` and avoids the heavier bridge
  vocabulary: no ZMod, no orderOf, no padicValNat, no p-adic integers, and no
  Witt vectors.

  Purpose:
    * provide small constructor/projection lemmas;
    * record the `r = 0` and `r = 1` elementary readings of `DepthAtLeast`;
    * keep the core predicates usable before connecting them to mathlib.
-/

import ABD.ApparitionDepth.Core

namespace ApparitionDepth

/-! ## Constructors -/

theorem firstAppearsAt_intro {ell p d : Nat}
    (hd_pos : 0 < d)
    (hd_app : AppearsAt ell p d)
    (hmin : ∀ m : Nat, 0 < m → m < d → ¬ AppearsAt ell p m) :
    FirstAppearsAt ell p d :=
  ⟨hd_pos, hd_app, hmin⟩

theorem exactDepth_intro {ell p d r : Nat}
    (hdepth : DepthAtLeast ell p d r)
    (hnot_next : ¬ DepthAtLeast ell p d (r + 1)) :
    ExactDepth ell p d r :=
  ⟨hdepth, hnot_next⟩

theorem firstWithDepth_intro {ell p d r : Nat}
    (hfirst : FirstAppearsAt ell p d)
    (hdepth : DepthAtLeast ell p d r) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  ⟨hfirst, hdepth⟩

theorem firstWithExact_intro {ell p d r : Nat}
    (hfirst : FirstAppearsAt ell p d)
    (hexact : ExactDepth ell p d r) :
    FirstAppearsWithExactDepth ell p d r :=
  ⟨hfirst, hexact⟩

/-! ## Iff forms for unfolding definitions -/

theorem firstAppearsAt_iff {ell p d : Nat} :
    FirstAppearsAt ell p d ↔
      0 < d ∧ AppearsAt ell p d ∧
        ∀ m : Nat, 0 < m → m < d → ¬ AppearsAt ell p m :=
  Iff.rfl

theorem exactDepth_iff {ell p d r : Nat} :
    ExactDepth ell p d r ↔
      DepthAtLeast ell p d r ∧ ¬ DepthAtLeast ell p d (r + 1) :=
  Iff.rfl

theorem firstWithDepth_iff {ell p d r : Nat} :
    FirstAppearsWithDepthAtLeast ell p d r ↔
      FirstAppearsAt ell p d ∧ DepthAtLeast ell p d r :=
  Iff.rfl

theorem firstWithExact_iff {ell p d r : Nat} :
    FirstAppearsWithExactDepth ell p d r ↔
      FirstAppearsAt ell p d ∧ ExactDepth ell p d r :=
  Iff.rfl

/-! ## Elementary readings of depth -/

/-- Depth at least zero is always true, since `p^0 = 1`. -/
theorem depthAtLeast_zero (ell p d : Nat) :
    DepthAtLeast ell p d 0 := by
  unfold DepthAtLeast
  simp

/-- Depth at least one is the same as ordinary appearance. -/
theorem depthAtLeast_one_iff {ell p d : Nat} :
    DepthAtLeast ell p d 1 ↔ AppearsAt ell p d := by
  unfold DepthAtLeast AppearsAt
  simp

/-- Ordinary appearance gives depth at least one. -/
theorem depthAtLeast_one_of_appears {ell p d : Nat}
    (h : AppearsAt ell p d) :
    DepthAtLeast ell p d 1 :=
  depthAtLeast_one_iff.mpr h

/-- Depth at least one gives ordinary appearance. -/
theorem appears_of_depthAtLeast_one {ell p d : Nat}
    (h : DepthAtLeast ell p d 1) :
    AppearsAt ell p d :=
  depthAtLeast_one_iff.mp h

/-! ## Convenience projections for combined predicates -/

theorem firstWithExact_appears {ell p d r : Nat}
    (h : FirstAppearsWithExactDepth ell p d r) :
    AppearsAt ell p d :=
  firstAppears_appears h.1

/-- If `p` first appears with exact depth `r`, then the depth is at least `r`. -/
theorem firstWithExact_depthAtLeast {ell p d r : Nat}
    (h : FirstAppearsWithExactDepth ell p d r) :
    DepthAtLeast ell p d r :=
  h.2.1

/-- If `p` first appears with exact depth `r`, then it does not have depth `r+1`. -/
theorem firstWithExact_not_next {ell p d r : Nat}
    (h : FirstAppearsWithExactDepth ell p d r) :
    ¬ DepthAtLeast ell p d (r + 1) :=
  h.2.2

end ApparitionDepth
