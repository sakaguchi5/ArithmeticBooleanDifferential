/-
  ABD.ApparitionDepth3.ZModBridge

  Independent bridge between the residue-ring statement
      (ell : ZMod (p^r))^d = 1
  and the core divisibility statement
      p^r ∣ ell^d - 1.
-/

import ABD.ApparitionDepth3.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq

namespace ApparitionDepth3

/-- `x` is a `d`-th root of unity modulo `p^r`. -/
def RootAtLevel (x p d r : Nat) : Prop :=
  ((x : ZMod (p ^ r)) ^ d = 1)

/-- Exact root-level statement: root at `r`, but not at `r+1`. -/
def ExactRootAtLevel (x p d r : Nat) : Prop :=
  RootAtLevel x p d r ∧ ¬ RootAtLevel x p d (r + 1)

@[simp]
theorem levelOneModulus_eq (p : Nat) : p ^ 1 = p := by
  simp

/-- The residue/Core bridge for a positive power `ell^d`.

The positivity is only needed because `N ell d` uses natural subtraction. -/
theorem rootAtLevel_iff_depthAtLeast_of_pow_pos {ell p d r : Nat}
    (hpos : 0 < ell ^ d) :
    RootAtLevel ell p d r ↔ DepthAtLeast ell p d r := by
  unfold RootAtLevel DepthAtLeast N
  rw [← Nat.cast_pow]
  rw [← Nat.cast_one]
  rw [ZMod.natCast_eq_natCast_iff (ell ^ d) 1 (p ^ r)]
  simpa [Nat.ModEq.comm] using
    (Nat.modEq_iff_dvd' (n := p ^ r) (a := 1) (b := ell ^ d) hpos)

/-- The canonical bridge for a positive base. -/
theorem rootAtLevel_iff_depthAtLeast_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell) :
    RootAtLevel ell p d r ↔ DepthAtLeast ell p d r :=
  rootAtLevel_iff_depthAtLeast_of_pow_pos (Nat.pow_pos hell_pos)

theorem depthAtLeast_of_rootAtLevel_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell)
    (hroot : RootAtLevel ell p d r) :
    DepthAtLeast ell p d r :=
  (rootAtLevel_iff_depthAtLeast_of_base_pos
    (ell := ell) (p := p) (d := d) (r := r) hell_pos).mp hroot

theorem rootAtLevel_of_depthAtLeast_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell)
    (hdepth : DepthAtLeast ell p d r) :
    RootAtLevel ell p d r :=
  (rootAtLevel_iff_depthAtLeast_of_base_pos
    (ell := ell) (p := p) (d := d) (r := r) hell_pos).mpr hdepth

/-- Exact root and exact depth agree for a positive base. -/
theorem exactRootAtLevel_iff_exactDepth_of_base_pos {ell p d r : Nat}
    (hell_pos : 0 < ell) :
    ExactRootAtLevel ell p d r ↔ ExactDepth ell p d r := by
  unfold ExactRootAtLevel ExactDepth
  constructor
  · intro h
    exact ⟨depthAtLeast_of_rootAtLevel_of_base_pos hell_pos h.1,
      fun hnext => h.2 (rootAtLevel_of_depthAtLeast_of_base_pos hell_pos hnext)⟩
  · intro h
    exact ⟨rootAtLevel_of_depthAtLeast_of_base_pos hell_pos h.1,
      fun hnext => h.2 (depthAtLeast_of_rootAtLevel_of_base_pos hell_pos hnext)⟩

end ApparitionDepth3
