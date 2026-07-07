/-
  ABD.ApparitionDepth.OrderAppearsBridge

  Step 9 of the Apparition-Depth Decomposition project.

  This file connects the `orderOf` / unit-group side to the Core apparition
  predicates.  As in the previous bridge layers, the hard equivalence between

      UnitPowOneAt ell p n hcop

  and

      AppearsAt ell p n

  is first represented as a named bridge predicate.  We then prove the safe
  structural consequences: an `OrderModIs` witness gives unit-level first
  apparition, and an agreement bridge transports it back to Core.
-/

import ABD.ApparitionDepth.NatDivisibilityBridge

namespace ApparitionDepth

/-- Agreement between unit-group power-one and Core appearance at a fixed
exponent `n`. -/
def UnitAppearsAgree (ell p n : Nat) (hcop : ell.Coprime p) : Prop :=
  UnitPowOneAt ell p n hcop ↔ AppearsAt ell p n

/-- Agreement between unit-level first appearance and Core first appearance. -/
def UnitFirstAppearsAgree (ell p d : Nat) (hcop : ell.Coprime p) : Prop :=
  UnitFirstPowOneAt ell p d hcop ↔ FirstAppearsAt ell p d

/-! ## Constructors and projections -/

theorem unitAppearsAgree_intro {ell p n : Nat} {hcop : ell.Coprime p}
    (h₁ : UnitPowOneAt ell p n hcop → AppearsAt ell p n)
    (h₂ : AppearsAt ell p n → UnitPowOneAt ell p n hcop) :
    UnitAppearsAgree ell p n hcop :=
  ⟨h₁, h₂⟩

theorem unitFirstAppearsAgree_intro {ell p d : Nat} {hcop : ell.Coprime p}
    (h₁ : UnitFirstPowOneAt ell p d hcop → FirstAppearsAt ell p d)
    (h₂ : FirstAppearsAt ell p d → UnitFirstPowOneAt ell p d hcop) :
    UnitFirstAppearsAgree ell p d hcop :=
  ⟨h₁, h₂⟩

theorem appearsAt_of_unitPowOneAt_of_agree {ell p n : Nat} {hcop : ell.Coprime p}
    (hbridge : UnitAppearsAgree ell p n hcop)
    (hunit : UnitPowOneAt ell p n hcop) :
    AppearsAt ell p n :=
  hbridge.mp hunit

theorem unitPowOneAt_of_appearsAt_of_agree {ell p n : Nat} {hcop : ell.Coprime p}
    (hbridge : UnitAppearsAgree ell p n hcop)
    (happ : AppearsAt ell p n) :
    UnitPowOneAt ell p n hcop :=
  hbridge.mpr happ

theorem firstAppearsAt_of_unitFirst_of_agree {ell p d : Nat} {hcop : ell.Coprime p}
    (hbridge : UnitFirstAppearsAgree ell p d hcop)
    (hunitFirst : UnitFirstPowOneAt ell p d hcop) :
    FirstAppearsAt ell p d :=
  hbridge.mp hunitFirst

theorem unitFirst_of_firstAppearsAt_of_agree {ell p d : Nat} {hcop : ell.Coprime p}
    (hbridge : UnitFirstAppearsAgree ell p d hcop)
    (hfirst : FirstAppearsAt ell p d) :
    UnitFirstPowOneAt ell p d hcop :=
  hbridge.mpr hfirst

/-! ## From order witnesses to first apparition -/

/-- If `d` is the unit-group order and `0 < d`, then `d` is the first positive
exponent where the unit power is one. -/
theorem unitFirstPowOneAt_of_orderModIs_pos {ell p d : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d) :
    UnitFirstPowOneAt ell p d hcop := by
  refine ⟨hd_pos, orderModIs_unitPowOneAt hord, ?_⟩
  intro m hm_pos hm_lt hpow
  have hdiv : d ∣ m := orderModIs_dvd_of_unitPowOneAt hord hpow
  have hle : d ≤ m := Nat.le_of_dvd hm_pos hdiv
  exact (not_lt_of_ge hle) hm_lt

/-- If `d` is the order and the unit/Core first-appearance bridge is available,
then `p` first appears at `d` in the Core sense. -/
theorem firstAppearsAt_of_orderModIs_pos_of_agree
    {ell p d : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hbridge : UnitFirstAppearsAgree ell p d hcop) :
    FirstAppearsAt ell p d :=
  hbridge.mp (unitFirstPowOneAt_of_orderModIs_pos hord hd_pos)

/-- The canonical `orderMod` gives unit-level first apparition, provided its
value is positive. -/
theorem unitFirstPowOneAt_orderMod {ell p : Nat} (hcop : ell.Coprime p)
    (hpos : 0 < orderMod ell p hcop) :
    UnitFirstPowOneAt ell p (orderMod ell p hcop) hcop :=
  unitFirstPowOneAt_of_orderModIs_pos (orderModIs_refl ell p hcop) hpos

/-- The canonical `orderMod` gives Core first apparition once the bridge is
available. -/
theorem firstAppearsAt_orderMod_of_agree {ell p : Nat} (hcop : ell.Coprime p)
    (hpos : 0 < orderMod ell p hcop)
    (hbridge : UnitFirstAppearsAgree ell p (orderMod ell p hcop) hcop) :
    FirstAppearsAt ell p (orderMod ell p hcop) :=
  hbridge.mp (unitFirstPowOneAt_orderMod hcop hpos)

end ApparitionDepth
