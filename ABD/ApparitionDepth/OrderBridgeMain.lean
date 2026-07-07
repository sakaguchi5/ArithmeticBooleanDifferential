/-
  ABD.ApparitionDepth.OrderBridgeMain

  Step 5 of the Apparition-Depth Decomposition project.

  This file gives the first usable "order witness" layer.  It still stays on
  the ZMod/orderOf side and does not yet prove the arithmetic equivalence with
  `AppearsAt`; that equivalence will be the next Nat-divisibility bridge.

  The main point here is:
    if `d = orderMod ell p hcop`, then `d` characterizes exactly the exponents
    `n` for which the unit represented by `ell` has `n`-th power one.
-/

import ABD.ApparitionDepth.OrderBridge

namespace ApparitionDepth

/-- `d` is the `orderOf`-based multiplicative order of `ell` modulo `p`.

This is a relation-level form, parallel to the Core style.  It keeps the bridge
usable without immediately choosing a notation like `d_p(ell)` as a function. -/
def OrderModIs (ell p d : Nat) (hcop : ell.Coprime p) : Prop :=
  orderMod ell p hcop = d

/-- Constructor for `OrderModIs`. -/
theorem orderModIs_intro {ell p d : Nat} (hcop : ell.Coprime p)
    (h : orderMod ell p hcop = d) :
    OrderModIs ell p d hcop :=
  h

/-- Projection from `OrderModIs`. -/
theorem orderModIs_eq {ell p d : Nat} {hcop : ell.Coprime p}
    (h : OrderModIs ell p d hcop) :
    orderMod ell p hcop = d :=
  h

/-- The canonical order witnesses itself. -/
theorem orderModIs_refl (ell p : Nat) (hcop : ell.Coprime p) :
    OrderModIs ell p (orderMod ell p hcop) hcop :=
  rfl

/-- If `d` is the order, then the `d`-th power is one. -/
theorem orderModIs_unitPowOneAt {ell p d : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop) :
    UnitPowOneAt ell p d hcop := by
  rw [← orderModIs_eq hord]
  exact orderMod_pow_eq_one hcop

/-- If `d` is the order, then `ell^n = 1` in the unit group exactly when
`d ∣ n`. -/
theorem orderModIs_dvd_iff_unitPowOneAt {ell p d n : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop) :
    d ∣ n ↔ UnitPowOneAt ell p n hcop := by
  rw [← orderModIs_eq hord]
  exact orderMod_dvd_iff_pow_eq_one hcop

/-- If `d` is the order and `d ∣ n`, then the `n`-th power is one. -/
theorem unitPowOneAt_of_orderModIs_dvd {ell p d n : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hdiv : d ∣ n) :
    UnitPowOneAt ell p n hcop :=
  (orderModIs_dvd_iff_unitPowOneAt hord).mp hdiv

/-- If `d` is the order and the `n`-th power is one, then `d ∣ n`. -/
theorem orderModIs_dvd_of_unitPowOneAt {ell p d n : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hpow : UnitPowOneAt ell p n hcop) :
    d ∣ n :=
  (orderModIs_dvd_iff_unitPowOneAt hord).mpr hpow

/-- A lightweight bridge from the functional order to the relation-level order. -/
theorem orderMod_eq_iff_orderModIs {ell p d : Nat} (hcop : ell.Coprime p) :
    orderMod ell p hcop = d ↔ OrderModIs ell p d hcop :=
  Iff.rfl

/-- Rewriting helper in the other direction. -/
theorem orderModIs_iff_orderMod_eq {ell p d : Nat} (hcop : ell.Coprime p) :
    OrderModIs ell p d hcop ↔ orderMod ell p hcop = d :=
  Iff.rfl

end ApparitionDepth
