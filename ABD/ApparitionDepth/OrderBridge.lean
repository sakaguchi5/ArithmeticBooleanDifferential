/-
  ABD.ApparitionDepth.OrderBridge

  Step 4 of the Apparition-Depth Decomposition project.

  This is the first light bridge from the elementary Core predicates to
  mathlib's multiplicative-order vocabulary.

  We deliberately keep this file small:
    * introduce the unit of `ZMod p` represented by the base `ell`;
    * define its order by `orderOf`;
    * record the basic `pow = 1` and divisibility characterizations inside
      `(ZMod p)^×`.

  This file does not yet identify `UnitPowOneAt` with the Core predicate
  `AppearsAt`.  That arithmetic divisibility bridge is postponed to the next
  layer so that the first `orderOf` connection remains robust.
-/

import ABD.ApparitionDepth.CoreExact
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace ApparitionDepth

/-- The unit of `ZMod p` represented by a natural number `ell`, assuming
`ell` is coprime to `p`.

Mathematically this is the residue class of the base `ell` in `(Z/pZ)^×`. -/
def unitMod (ell p : Nat) (hcop : ell.Coprime p) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime ell hcop

/-- The multiplicative order of the base `ell` modulo `p`, expressed in
mathlib's unit group `(ZMod p)^×`.

This is the mathlib-facing version of the future notation `d_p(ell)`. -/
noncomputable def orderMod (ell p : Nat) (hcop : ell.Coprime p) : Nat :=
  orderOf (unitMod ell p hcop)

/-- ZMod-native appearance: the residue class of `ell` has `n`-th power one
inside `(ZMod p)^×`.

The later arithmetic bridge will connect this to `AppearsAt ell p n`, i.e.
`p ∣ ell^n - 1`. -/
def UnitPowOneAt (ell p n : Nat) (hcop : ell.Coprime p) : Prop :=
  (unitMod ell p hcop) ^ n = 1

/-- ZMod-native first appearance: `d` is the first positive exponent where the
unit represented by `ell` has power one modulo `p`.

This mirrors `FirstAppearsAt`, but stays entirely in the unit group. -/
def UnitFirstPowOneAt (ell p d : Nat) (hcop : ell.Coprime p) : Prop :=
  0 < d ∧
    UnitPowOneAt ell p d hcop ∧
    ∀ m : Nat, 0 < m → m < d → ¬ UnitPowOneAt ell p m hcop

/-! ## Basic unfold/projection lemmas -/

@[simp]
theorem coe_unitMod {ell p : Nat} (hcop : ell.Coprime p) :
    ((unitMod ell p hcop : (ZMod p)ˣ) : ZMod p) = (ell : ZMod p) := by
  unfold unitMod
  simp only [ZMod.coe_unitOfCoprime ell hcop]

theorem orderMod_def {ell p : Nat} (hcop : ell.Coprime p) :
    orderMod ell p hcop = orderOf (unitMod ell p hcop) :=
  rfl

theorem unitPowOneAt_iff {ell p n : Nat} (hcop : ell.Coprime p) :
    UnitPowOneAt ell p n hcop ↔ (unitMod ell p hcop) ^ n = 1 :=
  Iff.rfl

/-- The order exponent always gives power one. -/
theorem orderMod_pow_eq_one {ell p : Nat} (hcop : ell.Coprime p) :
    UnitPowOneAt ell p (orderMod ell p hcop) hcop := by
  unfold UnitPowOneAt orderMod
  exact pow_orderOf_eq_one (unitMod ell p hcop)

/-- A power is one exactly when the order divides the exponent.

This is the central mathlib bridge for multiplicative order. -/
theorem orderMod_dvd_iff_pow_eq_one {ell p n : Nat} (hcop : ell.Coprime p) :
    orderMod ell p hcop ∣ n ↔ UnitPowOneAt ell p n hcop := by
  unfold UnitPowOneAt orderMod
  exact orderOf_dvd_iff_pow_eq_one

/-- If `n` is a multiple of the order, the unit has `n`-th power one. -/
theorem unitPowOneAt_of_orderMod_dvd {ell p n : Nat} (hcop : ell.Coprime p)
    (hdiv : orderMod ell p hcop ∣ n) :
    UnitPowOneAt ell p n hcop :=
  (orderMod_dvd_iff_pow_eq_one hcop).mp hdiv

/-- If the unit has `n`-th power one, then the order divides `n`. -/
theorem orderMod_dvd_of_unitPowOneAt {ell p n : Nat} (hcop : ell.Coprime p)
    (hpow : UnitPowOneAt ell p n hcop) :
    orderMod ell p hcop ∣ n :=
  (orderMod_dvd_iff_pow_eq_one hcop).mpr hpow

end ApparitionDepth
