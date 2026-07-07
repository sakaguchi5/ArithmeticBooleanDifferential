namespace ApparitionDepth

/-
  ApparitionDepth.Core

  Step 1 of the Apparition-Depth Decomposition project.

  This file intentionally avoids mathlib-heavy notions such as:
    * ZMod
    * orderOf
    * padicValNat
    * PadicInt
    * Witt vectors / Teichmuller lifts

  The goal of Core is only to name the elementary divisibility predicates.
  Later files can connect these predicates to mathlib's orderOf and p-adic valuation.
-/

/-- The basic sequence attached to a base `ell`: `N ell n = ell^n - 1`.

Mathematically, `ell` is intended to be the base prime, but this core definition
keeps it as a natural number. Prime assumptions are added only when needed. -/
def N (ell n : Nat) : Nat :=
  ell ^ n - 1

/-- `p` appears at exponent `n` for the base `ell` if `p ∣ ell^n - 1`. -/
def AppearsAt (ell p n : Nat) : Prop :=
  p ∣ N ell n

/-- `p` first appears at exponent `d` for base `ell`.

This is the relation-level version of the future notation `d_p(ell)`.
It avoids `Nat.find`, `orderOf`, and `ZMod` at the core layer. -/
def FirstAppearsAt (ell p d : Nat) : Prop :=
  0 < d ∧
  AppearsAt ell p d ∧
  ∀ m : Nat, 0 < m → m < d → ¬ AppearsAt ell p m

/-- The initial depth at exponent `d` is at least `r` if `p^r ∣ ell^d - 1`.

This is the relation-level version of `h_p(ell) ≥ r`, once `d` is known to be
the first apparition exponent. -/
def DepthAtLeast (ell p d r : Nat) : Prop :=
  p ^ r ∣ N ell d

/-- The depth at exponent `d` is exactly `r` if `p^r` divides but `p^(r+1)` does not. -/
def ExactDepth (ell p d r : Nat) : Prop :=
  DepthAtLeast ell p d r ∧ ¬ DepthAtLeast ell p d (r + 1)

/-- `p` first appears at `d`, and the initial depth is at least `r`. -/
def FirstAppearsWithDepthAtLeast (ell p d r : Nat) : Prop :=
  FirstAppearsAt ell p d ∧ DepthAtLeast ell p d r

/-- `p` first appears at `d`, and the initial depth is exactly `r`. -/
def FirstAppearsWithExactDepth (ell p d r : Nat) : Prop :=
  FirstAppearsAt ell p d ∧ ExactDepth ell p d r

/-! ## Small projection lemmas

These lemmas are deliberately elementary. They make later files easier without
bringing in heavier mathlib concepts.
-/

theorem firstAppears_pos {ell p d : Nat}
    (h : FirstAppearsAt ell p d) : 0 < d :=
  h.1

theorem firstAppears_appears {ell p d : Nat}
    (h : FirstAppearsAt ell p d) : AppearsAt ell p d :=
  h.2.1

theorem firstAppears_not_before {ell p d m : Nat}
    (h : FirstAppearsAt ell p d)
    (hm_pos : 0 < m)
    (hm_lt : m < d) : ¬ AppearsAt ell p m :=
  h.2.2 m hm_pos hm_lt

theorem exactDepth_depthAtLeast {ell p d r : Nat}
    (h : ExactDepth ell p d r) : DepthAtLeast ell p d r :=
  h.1

theorem exactDepth_not_next {ell p d r : Nat}
    (h : ExactDepth ell p d r) : ¬ DepthAtLeast ell p d (r + 1) :=
  h.2

theorem firstWithDepth_first {ell p d r : Nat}
    (h : FirstAppearsWithDepthAtLeast ell p d r) : FirstAppearsAt ell p d :=
  h.1

theorem firstWithDepth_depth {ell p d r : Nat}
    (h : FirstAppearsWithDepthAtLeast ell p d r) : DepthAtLeast ell p d r :=
  h.2

theorem firstWithExact_first {ell p d r : Nat}
    (h : FirstAppearsWithExactDepth ell p d r) : FirstAppearsAt ell p d :=
  h.1

theorem firstWithExact_exact {ell p d r : Nat}
    (h : FirstAppearsWithExactDepth ell p d r) : ExactDepth ell p d r :=
  h.2

theorem firstWithExact_depth {ell p d r : Nat}
    (h : FirstAppearsWithExactDepth ell p d r) : DepthAtLeast ell p d r :=
  exactDepth_depthAtLeast h.2

end ApparitionDepth
