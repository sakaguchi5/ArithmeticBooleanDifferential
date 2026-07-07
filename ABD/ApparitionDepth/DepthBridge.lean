/-
  ABD.ApparitionDepth.DepthBridge

  Step 6 of the Apparition-Depth Decomposition project.

  This file is the first light bridge from the Core depth predicates to
  mathlib's p-adic valuation vocabulary.

  Design rule:
    * keep `Core` relation-first and dependency-light;
    * introduce the valuation-facing function here;
    * do not yet force every Core predicate to be rewritten by valuation theorems.

  Later files can prove the stronger equivalence between `ExactDepth` and
  `padicValNat p (N ell d) = r` under the usual nonzero / prime assumptions.
-/

import ABD.ApparitionDepth.OrderBridgeMain
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace ApparitionDepth

/-- The valuation-facing version of initial depth at a chosen exponent `d`.

Mathematically, once `d` is known to be the first apparition exponent of `p`
for the base `ell`, this is the intended value of `h_p(ell)`:

`v_p(ell^d - 1)`.

This file only introduces the function.  The exact bridge to `ExactDepth` is
kept for a later theorem layer, because the strongest form needs the usual
side conditions on `p` and `N ell d`. -/
noncomputable def depthValue (ell p d : Nat) : Nat :=
  padicValNat p (N ell d)

/-- Relation-level wrapper for `depthValue ell p d = r`.

This mirrors the Core style: use relations first, then connect to functions. -/
def DepthValueIs (ell p d r : Nat) : Prop :=
  depthValue ell p d = r

/-- First apparition together with a valuation-facing depth value. -/
def FirstAppearsWithDepthValue (ell p d r : Nat) : Prop :=
  FirstAppearsAt ell p d ∧ DepthValueIs ell p d r

/-! ## Basic unfold/projection lemmas -/

theorem depthValue_def (ell p d : Nat) :
    depthValue ell p d = padicValNat p (N ell d) :=
  rfl

theorem depthValueIs_iff {ell p d r : Nat} :
    DepthValueIs ell p d r ↔ depthValue ell p d = r :=
  Iff.rfl

theorem depthValueIs_intro {ell p d r : Nat}
    (h : depthValue ell p d = r) :
    DepthValueIs ell p d r :=
  h

theorem depthValueIs_eq {ell p d r : Nat}
    (h : DepthValueIs ell p d r) :
    depthValue ell p d = r :=
  h

theorem firstWithDepthValue_intro {ell p d r : Nat}
    (hfirst : FirstAppearsAt ell p d)
    (hdepth : DepthValueIs ell p d r) :
    FirstAppearsWithDepthValue ell p d r :=
  ⟨hfirst, hdepth⟩

theorem firstWithDepthValue_first {ell p d r : Nat}
    (h : FirstAppearsWithDepthValue ell p d r) :
    FirstAppearsAt ell p d :=
  h.1

theorem firstWithDepthValue_depthValue {ell p d r : Nat}
    (h : FirstAppearsWithDepthValue ell p d r) :
    DepthValueIs ell p d r :=
  h.2

theorem firstWithDepthValue_depth_eq {ell p d r : Nat}
    (h : FirstAppearsWithDepthValue ell p d r) :
    depthValue ell p d = r :=
  h.2

/-! ## Compatibility wrappers with the Core exact-depth predicates -/

/-- A cautious bridge predicate saying that the Core exact-depth relation and the
valuation-facing depth value agree at the same `r`.

This is intentionally a predicate, not a theorem.  It lets later files state and
transport the compatibility without making this first valuation bridge heavy. -/
def ExactDepthAgreesWithValue (ell p d r : Nat) : Prop :=
  ExactDepth ell p d r ∧ DepthValueIs ell p d r

/-- First apparition plus exact-depth/value agreement. -/
def FirstAppearsWithAgreedDepthValue (ell p d r : Nat) : Prop :=
  FirstAppearsAt ell p d ∧ ExactDepthAgreesWithValue ell p d r

theorem exactDepthAgreesWithValue_intro {ell p d r : Nat}
    (hexact : ExactDepth ell p d r)
    (hvalue : DepthValueIs ell p d r) :
    ExactDepthAgreesWithValue ell p d r :=
  ⟨hexact, hvalue⟩

theorem exactDepthAgreesWithValue_exact {ell p d r : Nat}
    (h : ExactDepthAgreesWithValue ell p d r) :
    ExactDepth ell p d r :=
  h.1

theorem exactDepthAgreesWithValue_value {ell p d r : Nat}
    (h : ExactDepthAgreesWithValue ell p d r) :
    DepthValueIs ell p d r :=
  h.2

theorem firstWithAgreedDepthValue_intro {ell p d r : Nat}
    (hfirst : FirstAppearsAt ell p d)
    (hagrees : ExactDepthAgreesWithValue ell p d r) :
    FirstAppearsWithAgreedDepthValue ell p d r :=
  ⟨hfirst, hagrees⟩

theorem firstWithAgreedDepthValue_first {ell p d r : Nat}
    (h : FirstAppearsWithAgreedDepthValue ell p d r) :
    FirstAppearsAt ell p d :=
  h.1

theorem firstWithAgreedDepthValue_exact {ell p d r : Nat}
    (h : FirstAppearsWithAgreedDepthValue ell p d r) :
    ExactDepth ell p d r :=
  h.2.1

theorem firstWithAgreedDepthValue_value {ell p d r : Nat}
    (h : FirstAppearsWithAgreedDepthValue ell p d r) :
    DepthValueIs ell p d r :=
  h.2.2

end ApparitionDepth
