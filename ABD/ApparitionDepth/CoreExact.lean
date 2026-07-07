/-
  ABD.ApparitionDepth.CoreExact

  Step 2b of the Apparition-Depth Decomposition project.

  This file isolates the "exact depth" layer.  We keep the main Core predicate
  `ExactDepth ell p d r` unchanged, but add a positive wrapper for the intended
  mathematical use: initial depths are normally considered with `1 ≤ r`.

  Still no heavy mathlib bridge vocabulary is used here.
-/

import ABD.ApparitionDepth.CoreBasic

namespace ApparitionDepth

/-- The intended positive version of exact depth: exact depth `r` together with `0 < r`.

The raw `ExactDepth` predicate is kept available for elementary statements, but most
future apparition-depth statements should use this wrapper or assume `0 < r`. -/
def PositiveExactDepth (ell p d r : Nat) : Prop :=
  0 < r ∧ ExactDepth ell p d r

/-- First apparition together with a positive exact depth. -/
def FirstAppearsWithPositiveExactDepth (ell p d r : Nat) : Prop :=
  FirstAppearsAt ell p d ∧ PositiveExactDepth ell p d r

/-! ## Constructors and projections -/

theorem positiveExactDepth_intro {ell p d r : Nat}
    (hr_pos : 0 < r)
    (hexact : ExactDepth ell p d r) :
    PositiveExactDepth ell p d r :=
  ⟨hr_pos, hexact⟩

theorem positiveExactDepth_pos {ell p d r : Nat}
    (h : PositiveExactDepth ell p d r) :
    0 < r :=
  h.1

theorem positiveExactDepth_exact {ell p d r : Nat}
    (h : PositiveExactDepth ell p d r) :
    ExactDepth ell p d r :=
  h.2

theorem positiveExactDepth_depthAtLeast {ell p d r : Nat}
    (h : PositiveExactDepth ell p d r) :
    DepthAtLeast ell p d r :=
  h.2.1

theorem positiveExactDepth_not_next {ell p d r : Nat}
    (h : PositiveExactDepth ell p d r) :
    ¬ DepthAtLeast ell p d (r + 1) :=
  h.2.2

theorem firstWithPositiveExact_intro {ell p d r : Nat}
    (hfirst : FirstAppearsAt ell p d)
    (hposExact : PositiveExactDepth ell p d r) :
    FirstAppearsWithPositiveExactDepth ell p d r :=
  ⟨hfirst, hposExact⟩

theorem firstWithPositiveExact_first {ell p d r : Nat}
    (h : FirstAppearsWithPositiveExactDepth ell p d r) :
    FirstAppearsAt ell p d :=
  h.1

theorem firstWithPositiveExact_positiveExact {ell p d r : Nat}
    (h : FirstAppearsWithPositiveExactDepth ell p d r) :
    PositiveExactDepth ell p d r :=
  h.2

theorem firstWithPositiveExact_pos {ell p d r : Nat}
    (h : FirstAppearsWithPositiveExactDepth ell p d r) :
    0 < r :=
  h.2.1

theorem firstWithPositiveExact_exact {ell p d r : Nat}
    (h : FirstAppearsWithPositiveExactDepth ell p d r) :
    ExactDepth ell p d r :=
  h.2.2

theorem firstWithPositiveExact_depthAtLeast {ell p d r : Nat}
    (h : FirstAppearsWithPositiveExactDepth ell p d r) :
    DepthAtLeast ell p d r :=
  h.2.2.1

theorem firstWithPositiveExact_not_next {ell p d r : Nat}
    (h : FirstAppearsWithPositiveExactDepth ell p d r) :
    ¬ DepthAtLeast ell p d (r + 1) :=
  h.2.2.2

/-! ## Exact-depth incompatibility lemmas -/

/-- If depth at least `r+1` holds, exact depth `r` is impossible. -/
theorem not_exactDepth_of_depthAtLeast_next {ell p d r : Nat}
    (hnext : DepthAtLeast ell p d (r + 1)) :
    ¬ ExactDepth ell p d r := by
  intro hexact
  exact hexact.2 hnext

/-- Exact depth `r` and exact depth `r+1` cannot both hold. -/
theorem exactDepth_not_exactDepth_succ {ell p d r : Nat}
    (hr : ExactDepth ell p d r) :
    ¬ ExactDepth ell p d (r + 1) := by
  intro hs
  exact hr.2 hs.1

/-- Exact depth one means appearance, but not depth at least two. -/
theorem exactDepth_one_iff {ell p d : Nat} :
    ExactDepth ell p d 1 ↔
      AppearsAt ell p d ∧ ¬ DepthAtLeast ell p d 2 := by
  unfold ExactDepth
  rw [depthAtLeast_one_iff]

/-- Positive exact depth can be unpacked as `0 < r`, depth at least `r`, and not depth `r+1`. -/
theorem positiveExactDepth_iff {ell p d r : Nat} :
    PositiveExactDepth ell p d r ↔
      0 < r ∧ DepthAtLeast ell p d r ∧ ¬ DepthAtLeast ell p d (r + 1) := by
  unfold PositiveExactDepth ExactDepth
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2⟩
  · intro h
    exact ⟨h.1, ⟨h.2.1, h.2.2⟩⟩

end ApparitionDepth
