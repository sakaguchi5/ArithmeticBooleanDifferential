/-
  ABD.ApparitionDepth.MovingBase

  Step 7 of the Apparition-Depth Decomposition project.

  This file introduces a lightweight residue-ring language for the moving-base
  side of the theory.

  Guiding idea:
    fixing a target prime `p`, an exponent/order candidate `d`, and a precision
    `r`, a base `ell` is generated only up to its residue class modulo `p^r`.

  This first file stays on the `ZMod (p^r)` side.  The arithmetic theorem

      ((ell : ZMod (p^r))^d = 1)  <->  p^r ∣ ell^d - 1

  is intentionally left to a later Nat-divisibility bridge.
-/

import ABD.ApparitionDepth.DepthBridge
import Mathlib.Data.ZMod.Basic

namespace ApparitionDepth

/-- Residue-ring depth at least `r`: the base `ell` has `d`-th power one in
`ZMod (p^r)`.

This is the moving-base side analogue of `DepthAtLeast ell p d r`, but kept in
`ZMod` form for now. -/
def ResidueDepthAtLeast (ell p d r : Nat) : Prop :=
  ((ell : ZMod (p ^ r)) ^ d = 1)

/-- Exact residue depth at `r`: power one modulo `p^r`, but not modulo
`p^(r+1)`.

This mirrors `ExactDepth`, again on the residue-ring side. -/
def ResidueExactDepth (ell p d r : Nat) : Prop :=
  ResidueDepthAtLeast ell p d r ∧ ¬ ResidueDepthAtLeast ell p d (r + 1)

/-- A moving-base residue certificate.

`omega` is the generated representative modulo `p^r`; `ell` is any base in the
same residue class.  If `omega^d = 1` in `ZMod (p^r)`, then `ell^d = 1` there
as well. -/
def MovingBaseClass (ell omega p d r : Nat) : Prop :=
  (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) ∧
    ResidueDepthAtLeast omega p d r

/-- Exact moving-base residue certificate. -/
def MovingBaseExactClass (ell omega p d r : Nat) : Prop :=
  (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) ∧
    ResidueExactDepth omega p d r

/-! ## Basic unfold/projection lemmas -/

theorem residueDepthAtLeast_iff {ell p d r : Nat} :
    ResidueDepthAtLeast ell p d r ↔ ((ell : ZMod (p ^ r)) ^ d = 1) :=
  Iff.rfl

theorem residueExactDepth_iff {ell p d r : Nat} :
    ResidueExactDepth ell p d r ↔
      ResidueDepthAtLeast ell p d r ∧ ¬ ResidueDepthAtLeast ell p d (r + 1) :=
  Iff.rfl

theorem residueExactDepth_depthAtLeast {ell p d r : Nat}
    (h : ResidueExactDepth ell p d r) :
    ResidueDepthAtLeast ell p d r :=
  h.1

theorem residueExactDepth_not_next {ell p d r : Nat}
    (h : ResidueExactDepth ell p d r) :
    ¬ ResidueDepthAtLeast ell p d (r + 1) :=
  h.2

theorem movingBaseClass_congr {ell omega p d r : Nat}
    (h : MovingBaseClass ell omega p d r) :
    (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) :=
  h.1

theorem movingBaseClass_omegaDepth {ell omega p d r : Nat}
    (h : MovingBaseClass ell omega p d r) :
    ResidueDepthAtLeast omega p d r :=
  h.2

/-- Transport residue depth along a moving-base residue certificate. -/
theorem movingBaseClass_residueDepthAtLeast {ell omega p d r : Nat}
    (h : MovingBaseClass ell omega p d r) :
    ResidueDepthAtLeast ell p d r := by
  unfold ResidueDepthAtLeast
  rw [h.1]
  exact h.2

theorem movingBaseExactClass_congr {ell omega p d r : Nat}
    (h : MovingBaseExactClass ell omega p d r) :
    (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) :=
  h.1

theorem movingBaseExactClass_omegaExact {ell omega p d r : Nat}
    (h : MovingBaseExactClass ell omega p d r) :
    ResidueExactDepth omega p d r :=
  h.2

/-- Exact certificates also give ordinary moving-base certificates at level `r`. -/
theorem movingBaseClass_of_exact {ell omega p d r : Nat}
    (h : MovingBaseExactClass ell omega p d r) :
    MovingBaseClass ell omega p d r :=
  ⟨h.1, h.2.1⟩

/-- Transport exact residue depth's positive part along a moving-base exact
certificate.  The negative `r+1` part is deliberately kept on `omega`; transporting
it to `ell` requires comparing residue classes modulo `p^(r+1)`, which is a
separate stronger condition. -/
theorem movingBaseExactClass_residueDepthAtLeast {ell omega p d r : Nat}
    (h : MovingBaseExactClass ell omega p d r) :
    ResidueDepthAtLeast ell p d r :=
  movingBaseClass_residueDepthAtLeast (movingBaseClass_of_exact h)

end ApparitionDepth
