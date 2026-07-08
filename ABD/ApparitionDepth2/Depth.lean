/-
  ABD.ApparitionDepth2.Depth

  Optional depth-value layer.  The main public path should use
  `DepthAtLeast`; `depthValue` is kept as a side bridge for exact-depth and
  valuation-style statements.
-/

import ABD.ApparitionDepth.DepthValueBridgeProof
import ABD.ApparitionDepth2.ZModBridge

namespace ApparitionDepth2

/-- Archived valuation-style depth function. -/
noncomputable abbrev depthValue (ell p d : Nat) : Nat :=
  ApparitionDepth.depthValue ell p d

/-- `DepthAtLeast` is equivalent to a lower bound on `depthValue`. -/
theorem depthAtLeast_iff_le_depthValue {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0) :
    DepthAtLeast ell p d r ↔ r ≤ depthValue ell p d :=
  ApparitionDepth.depthAtLeast_iff_le_depthValue hN

/-- Forward direction to the valuation-style depth value. -/
theorem le_depthValue_of_depthAtLeast {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hdepth : DepthAtLeast ell p d r) :
    r ≤ depthValue ell p d :=
  ApparitionDepth.le_depthValue_of_depthAtLeast hN hdepth

/-- Reverse direction from the valuation-style depth value. -/
theorem depthAtLeast_of_le_depthValue {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (hle : r ≤ depthValue ell p d) :
    DepthAtLeast ell p d r :=
  ApparitionDepth.depthAtLeast_of_le_depthValue hN hle

/-- Exact depth equals equality of the depth value. -/
theorem exactDepth_iff_depthValue_eq {ell p d r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0) :
    ExactDepth ell p d r ↔ depthValue ell p d = r :=
  ApparitionDepth.exactDepth_iff_depthValue_eq hN

end ApparitionDepth2
