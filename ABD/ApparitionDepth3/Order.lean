/-
  ABD.ApparitionDepth3.Order

  Independent order-of-apparition bridge.
-/

import ABD.ApparitionDepth3.ZModBridge
import Mathlib.GroupTheory.OrderOfElement

namespace ApparitionDepth3

/-- The unit of `ZMod p` represented by `ell`. -/
def unitMod (ell p : Nat) (hcop : ell.Coprime p) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime ell hcop

/-- Multiplicative order of `ell` modulo `p`. -/
noncomputable def orderMod (ell p : Nat) (hcop : ell.Coprime p) : Nat :=
  orderOf (unitMod ell p hcop)

/-- Unit-level power-one. -/
def UnitPowOneAt (ell p n : Nat) (hcop : ell.Coprime p) : Prop :=
  (unitMod ell p hcop) ^ n = 1

/-- Relation-level statement that `d` is the order of `ell` modulo `p`. -/
def OrderModIs (ell p d : Nat) (hcop : ell.Coprime p) : Prop :=
  orderMod ell p hcop = d

@[simp]
theorem coe_unitMod {ell p : Nat} (hcop : ell.Coprime p) :
    ((unitMod ell p hcop : (ZMod p)ˣ) : ZMod p) = (ell : ZMod p) := by
  unfold unitMod
  simp only [ZMod.coe_unitOfCoprime ell hcop]

theorem orderMod_pow_eq_one {ell p : Nat} (hcop : ell.Coprime p) :
    UnitPowOneAt ell p (orderMod ell p hcop) hcop := by
  unfold UnitPowOneAt orderMod
  exact pow_orderOf_eq_one (unitMod ell p hcop)

theorem orderMod_dvd_iff_pow_eq_one {ell p n : Nat} (hcop : ell.Coprime p) :
    orderMod ell p hcop ∣ n ↔ UnitPowOneAt ell p n hcop := by
  unfold UnitPowOneAt orderMod
  exact orderOf_dvd_iff_pow_eq_one

theorem orderModIs_unitPowOneAt {ell p d : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop) :
    UnitPowOneAt ell p d hcop := by
  rw [← hord]
  exact orderMod_pow_eq_one hcop

theorem orderModIs_dvd_of_unitPowOneAt {ell p d n : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hpow : UnitPowOneAt ell p n hcop) :
    d ∣ n := by
  rw [← hord]
  exact (orderMod_dvd_iff_pow_eq_one hcop).mpr hpow

/-- Unit power-one is the same as residue power-one. -/
theorem unitPowOneAt_iff_residuePowOne {ell p n : Nat} (hcop : ell.Coprime p) :
    UnitPowOneAt ell p n hcop ↔ ((ell : ZMod p) ^ n = 1) := by
  constructor
  · intro hunit
    have hcast := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hunit
    simpa [UnitPowOneAt, coe_unitMod] using hcast
  · intro hres
    unfold UnitPowOneAt
    apply Units.ext
    simpa [coe_unitMod] using hres

/-- Residue power-one modulo `p` is equivalent to Core appearance.

This is the arithmetic bridge that was previously isolated as a placeholder:

`((ell : ZMod p)^n = 1) <-> p ∣ ell^n - 1`.

The proof goes through `ZMod.natCast_eq_natCast_iff` and
`Nat.modEq_iff_dvd'`.  The positivity assumption gives `1 <= ell^n`, needed
because `N ell n` uses natural subtraction. -/
theorem residuePowOne_iff_appearsAt_of_pow_pos {ell p n : Nat}
    (hpos : 0 < ell ^ n) :
    ((ell : ZMod p) ^ n = 1) ↔ AppearsAt ell p n := by
  unfold AppearsAt N
  rw [← Nat.cast_pow]
  rw [← Nat.cast_one]
  rw [ZMod.natCast_eq_natCast_iff (ell ^ n) 1 p]
  simpa [Nat.ModEq.comm] using
    (Nat.modEq_iff_dvd' (n := p) (a := 1) (b := ell ^ n) hpos)

/-- Residue power-one modulo `p` is ordinary appearance. -/
theorem residuePowOne_iff_appearsAt_of_base_pos {ell p n : Nat}
    (hell_pos : 0 < ell) :
    ((ell : ZMod p) ^ n = 1) ↔ AppearsAt ell p n :=
  residuePowOne_iff_appearsAt_of_pow_pos (Nat.pow_pos hell_pos)


/-- Unit power-one modulo `p` is ordinary appearance. -/
theorem unitPowOneAt_iff_appearsAt_of_base_pos {ell p n : Nat}
    {hcop : ell.Coprime p}
    (hell_pos : 0 < ell) :
    UnitPowOneAt ell p n hcop ↔ AppearsAt ell p n := by
  rw [unitPowOneAt_iff_residuePowOne hcop]
  exact residuePowOne_iff_appearsAt_of_base_pos hell_pos

/-- If `d` is the multiplicative order and `d > 0`, then `p` first appears at `d`. -/
theorem firstAppearsAt_of_orderModIs_pos_of_base_pos
    {ell p d : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hell_pos : 0 < ell) :
    FirstAppearsAt ell p d := by
  refine firstAppearsAt_intro hd_pos ?_ ?_
  · exact (unitPowOneAt_iff_appearsAt_of_base_pos
      (ell := ell) (p := p) (n := d) (hcop := hcop) hell_pos).mp
      (orderModIs_unitPowOneAt hord)
  · intro m hm_pos hm_lt happ
    have hunit : UnitPowOneAt ell p m hcop :=
      (unitPowOneAt_iff_appearsAt_of_base_pos
        (ell := ell) (p := p) (n := m) (hcop := hcop) hell_pos).mpr happ
    have hdiv : d ∣ m := orderModIs_dvd_of_unitPowOneAt hord hunit
    have hle : d ≤ m := Nat.le_of_dvd hm_pos hdiv
    exact (not_lt_of_ge hle) hm_lt

/-- Pack order control and depth control. -/
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

end ApparitionDepth3
