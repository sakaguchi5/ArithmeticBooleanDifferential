/-
  ABD.ApparitionDepth2.Order

  Public bridge between multiplicative order modulo `p` and first apparition.

  Public theorem theme:
    ord_p(ell) = d  ->  FirstAppearsAt ell p d.
-/

import ABD.ApparitionDepth.UnitAppearsBridgeProof
import ABD.ApparitionDepth2.Basic

namespace ApparitionDepth2

/-- Relation-level statement that `d` is the multiplicative order of `ell` mod `p`. -/
abbrev OrderModIs (ell p d : Nat) (hcop : ell.Coprime p) : Prop :=
  ApparitionDepth.OrderModIs ell p d hcop

/-- Function-level order used by the archived development. -/
noncomputable abbrev orderMod (ell p : Nat) (hcop : ell.Coprime p) : Nat :=
  ApparitionDepth.orderMod ell p hcop

/-- If `d` is the multiplicative order and `d > 0`, then `p` first appears at `d`. -/
theorem firstAppearsAt_of_orderModIs_pos_of_base_pos
    {ell p d : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hell_pos : 0 < ell) :
    FirstAppearsAt ell p d :=
  ApparitionDepth.firstAppearsAt_of_orderModIs_pos_of_base_pos hord hd_pos hell_pos

/-- Canonical order form of first apparition. -/
theorem firstAppearsAt_orderMod_of_base_pos
    {ell p : Nat} (hcop : ell.Coprime p)
    (hpos_order : 0 < orderMod ell p hcop)
    (hell_pos : 0 < ell) :
    FirstAppearsAt ell p (orderMod ell p hcop) :=
  ApparitionDepth.firstAppearsAt_orderMod_of_base_pos hcop hpos_order hell_pos

/-- Pack order and depth into the public first-with-depth predicate. -/
theorem firstWithDepth_of_order_and_depth
    {ell p d r : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hell_pos : 0 < ell)
    (hdepth : DepthAtLeast ell p d r) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  firstWithDepth_intro
    (firstAppearsAt_of_orderModIs_pos_of_base_pos hord hd_pos hell_pos)
    hdepth

end ApparitionDepth2
