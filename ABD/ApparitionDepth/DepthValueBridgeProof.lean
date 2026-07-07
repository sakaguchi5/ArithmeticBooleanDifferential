/-
  ABD.ApparitionDepth.DepthValueBridgeProof

  Step 12 of the Apparition-Depth Decomposition project.

  This file proves the bridge between the Core exact-depth predicates and the
  valuation-facing function introduced in `DepthBridge`:

      depthValue ell p d = padicValNat p (N ell d)

  Under the standard assumptions that `p` is prime and `N ell d` is nonzero,
  Core divisibility depth is equivalent to comparison with `depthValue`, and
  exact Core depth is equivalent to equality with `depthValue`.
-/

import ABD.ApparitionDepth.ResidueDepthBridgeProof

namespace ApparitionDepth

/-! ## Depth-at-least as a comparison with `depthValue` -/

/-- Core depth at least `r` is equivalent to `r <= depthValue ell p d`, assuming
`p` is prime and the target number `N ell d` is nonzero.

This is the direct bridge from the relation-level predicate

`p^r ∣ N ell d`

to mathlib's `padicValNat`. -/
theorem depthAtLeast_iff_le_depthValue {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0) :
    DepthAtLeast ell p d r ↔ r ≤ depthValue ell p d := by
  unfold DepthAtLeast depthValue
  exact padicValNat_dvd_iff_le hN

/-- Forward direction of `depthAtLeast_iff_le_depthValue`. -/
theorem le_depthValue_of_depthAtLeast {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hdepth : DepthAtLeast ell p d r) :
    r ≤ depthValue ell p d :=
  (depthAtLeast_iff_le_depthValue (ell := ell) (p := p) (d := d) (r := r) hN).mp hdepth

/-- Reverse direction of `depthAtLeast_iff_le_depthValue`. -/
theorem depthAtLeast_of_le_depthValue {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hle : r ≤ depthValue ell p d) :
    DepthAtLeast ell p d r :=
  (depthAtLeast_iff_le_depthValue (ell := ell) (p := p) (d := d) (r := r) hN).mpr hle

/-! ## Exact depth as equality with `depthValue` -/

/-- Exact Core depth `r` is equivalent to `depthValue ell p d = r`, assuming
`p` is prime and `N ell d` is nonzero. -/
theorem exactDepth_iff_depthValue_eq {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0) :
    ExactDepth ell p d r ↔ depthValue ell p d = r := by
  unfold ExactDepth
  rw [depthAtLeast_iff_le_depthValue (ell := ell) (p := p) (d := d) (r := r) hN]
  rw [depthAtLeast_iff_le_depthValue (ell := ell) (p := p) (d := d) (r := r + 1) hN]
  constructor
  · intro h
    have hv_lt : depthValue ell p d < r + 1 := not_le.mp h.2
    have hv_le : depthValue ell p d ≤ r := Nat.lt_succ_iff.mp hv_lt
    exact le_antisymm hv_le h.1
  · intro hv
    constructor
    · rw [hv]
    · rw [hv]
      exact Nat.not_succ_le_self r

/-- Forward direction: exact Core depth gives the valuation-facing depth value. -/
theorem depthValue_eq_of_exactDepth {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hexact : ExactDepth ell p d r) :
    depthValue ell p d = r :=
  (exactDepth_iff_depthValue_eq (ell := ell) (p := p) (d := d) (r := r) hN).mp hexact

/-- Reverse direction: the valuation-facing depth value gives exact Core depth. -/
theorem exactDepth_of_depthValue_eq {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hvalue : depthValue ell p d = r) :
    ExactDepth ell p d r :=
  (exactDepth_iff_depthValue_eq (ell := ell) (p := p) (d := d) (r := r) hN).mpr hvalue

/-! ## Filling the named value predicates from `DepthBridge` -/

/-- Exact Core depth produces the named value relation `DepthValueIs`. -/
theorem depthValueIs_of_exactDepth {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hexact : ExactDepth ell p d r) :
    DepthValueIs ell p d r :=
  depthValueIs_intro (depthValue_eq_of_exactDepth (ell := ell) (p := p) (d := d) (r := r) hN hexact)

/-- A named value relation produces exact Core depth. -/
theorem exactDepth_of_depthValueIs {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hvalue : DepthValueIs ell p d r) :
    ExactDepth ell p d r :=
  exactDepth_of_depthValue_eq (ell := ell) (p := p) (d := d) (r := r) hN (depthValueIs_eq hvalue)

/-- The Core exact-depth relation and the valuation-facing depth value agree
whenever exact depth is known. -/
theorem exactDepthAgreesWithValue_of_exactDepth {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hexact : ExactDepth ell p d r) :
    ExactDepthAgreesWithValue ell p d r :=
  exactDepthAgreesWithValue_intro hexact
    (depthValueIs_of_exactDepth (ell := ell) (p := p) (d := d) (r := r) hN hexact)

/-- The Core exact-depth relation and the valuation-facing depth value agree
whenever the valuation value is known. -/
theorem exactDepthAgreesWithValue_of_depthValueIs {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hvalue : DepthValueIs ell p d r) :
    ExactDepthAgreesWithValue ell p d r :=
  exactDepthAgreesWithValue_intro
    (exactDepth_of_depthValueIs (ell := ell) (p := p) (d := d) (r := r) hN hvalue)
    hvalue

/-- First apparition plus exact depth gives first apparition plus agreed
valuation depth. -/
theorem firstWithAgreedDepthValue_of_firstWithExact {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (h : FirstAppearsWithExactDepth ell p d r) :
    FirstAppearsWithAgreedDepthValue ell p d r :=
  firstWithAgreedDepthValue_intro h.1
    (exactDepthAgreesWithValue_of_exactDepth (ell := ell) (p := p) (d := d) (r := r) hN h.2)

/-- First apparition plus a valuation-facing depth value gives first apparition
plus exact Core depth. -/
theorem firstWithExact_of_firstWithDepthValue {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (h : FirstAppearsWithDepthValue ell p d r) :
    FirstAppearsWithExactDepth ell p d r :=
  firstWithExact_intro h.1
    (exactDepth_of_depthValueIs (ell := ell) (p := p) (d := d) (r := r) hN h.2)

end ApparitionDepth
