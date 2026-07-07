/-
  ABD.ApparitionDepth.UnitAppearsBridgeProof

  Step 10 of the Apparition-Depth Decomposition project.

  This file proves the actual bridge

      UnitPowOneAt ell p n hcop  <->  AppearsAt ell p n

  under the natural side condition `0 < ell`.  This avoids the earlier
  placeholder `ResidueAppearsAgree`: the residue/Nat agreement is proved here.

  The condition `0 < ell` is mathematically harmless for the intended use,
  where `ell` is a base prime.  It is useful because Core defines

      N ell n = ell^n - 1

  using natural subtraction, so rewriting modular equality as divisibility of
  `ell^n - 1` needs `1 <= ell^n`.
-/

import ABD.ApparitionDepth.OrderAppearsBridge
import Mathlib.Data.Nat.ModEq

namespace ApparitionDepth

/-! ## Residue-level appearance is ordinary divisibility appearance -/

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

/-- The same bridge in the intended base-positive form. -/
theorem residuePowOne_iff_appearsAt_of_base_pos {ell p n : Nat}
    (hell_pos : 0 < ell) :
    ((ell : ZMod p) ^ n = 1) ↔ AppearsAt ell p n :=
  residuePowOne_iff_appearsAt_of_pow_pos (Nat.pow_pos hell_pos)

/-! ## Removing the unit wrapper -/

/-- Unit-level power-one is equivalent to residue-level power-one. -/
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

/-- Full unit/Core agreement, proved directly from the residue/Nat bridge. -/
theorem unitAppearsAgree_of_base_pos {ell p n : Nat} {hcop : ell.Coprime p}
    (hell_pos : 0 < ell) :
    UnitAppearsAgree ell p n hcop := by
  unfold UnitAppearsAgree
  rw [unitPowOneAt_iff_residuePowOne hcop]
  exact residuePowOne_iff_appearsAt_of_base_pos hell_pos

/-- Forward direction of the full bridge. -/
theorem appearsAt_of_unitPowOneAt_of_base_pos {ell p n : Nat} {hcop : ell.Coprime p}
    (hell_pos : 0 < ell)
    (hunit : UnitPowOneAt ell p n hcop) :
    AppearsAt ell p n :=
  (unitAppearsAgree_of_base_pos (ell := ell) (p := p) (n := n) (hcop := hcop)
    hell_pos).mp hunit

/-- Reverse direction of the full bridge. -/
theorem unitPowOneAt_of_appearsAt_of_base_pos {ell p n : Nat} {hcop : ell.Coprime p}
    (hell_pos : 0 < ell)
    (happ : AppearsAt ell p n) :
    UnitPowOneAt ell p n hcop :=
  (unitAppearsAgree_of_base_pos (ell := ell) (p := p) (n := n) (hcop := hcop)
    hell_pos).mpr happ

/-! ## First-appearance transport -/

/-- Pointwise unit/Core agreement at all exponents gives agreement of the
first-appearance predicates at `d`. -/
theorem unitFirstAppearsAgree_of_forall_unitAppearsAgree
    {ell p d : Nat} {hcop : ell.Coprime p}
    (hagree : ∀ n : Nat, UnitAppearsAgree ell p n hcop) :
    UnitFirstAppearsAgree ell p d hcop := by
  unfold UnitFirstAppearsAgree UnitFirstPowOneAt FirstAppearsAt
  constructor
  · intro hunitFirst
    refine ⟨hunitFirst.1, ?_, ?_⟩
    · exact (hagree d).mp hunitFirst.2.1
    · intro m hm_pos hm_lt happ
      exact hunitFirst.2.2 m hm_pos hm_lt ((hagree m).mpr happ)
  · intro hfirst
    refine ⟨hfirst.1, ?_, ?_⟩
    · exact (hagree d).mpr hfirst.2.1
    · intro m hm_pos hm_lt hunit
      exact hfirst.2.2 m hm_pos hm_lt ((hagree m).mp hunit)

/-- Positive base gives agreement of unit-level and Core first appearance. -/
theorem unitFirstAppearsAgree_of_base_pos
    {ell p d : Nat} {hcop : ell.Coprime p}
    (hell_pos : 0 < ell) :
    UnitFirstAppearsAgree ell p d hcop :=
  unitFirstAppearsAgree_of_forall_unitAppearsAgree
    (fun n => unitAppearsAgree_of_base_pos (ell := ell) (p := p) (n := n)
      (hcop := hcop) hell_pos)

/-- If `d` is the order and `ell` is positive, then `p` first appears at `d`
in the Core sense, assuming `0 < d`. -/
theorem firstAppearsAt_of_orderModIs_pos_of_base_pos
    {ell p d : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hell_pos : 0 < ell) :
    FirstAppearsAt ell p d :=
  firstAppearsAt_of_orderModIs_pos_of_agree hord hd_pos
    (unitFirstAppearsAgree_of_base_pos (ell := ell) (p := p) (d := d)
      (hcop := hcop) hell_pos)

/-- The canonical `orderMod` gives Core first apparition for positive bases,
provided the order is positive. -/
theorem firstAppearsAt_orderMod_of_base_pos
    {ell p : Nat} (hcop : ell.Coprime p)
    (hpos_order : 0 < orderMod ell p hcop)
    (hell_pos : 0 < ell) :
    FirstAppearsAt ell p (orderMod ell p hcop) :=
  firstAppearsAt_orderMod_of_agree hcop hpos_order
    (unitFirstAppearsAgree_of_base_pos (ell := ell) (p := p)
      (d := orderMod ell p hcop) (hcop := hcop) hell_pos)

end ApparitionDepth
