/-
  ABD.ApparitionDepth3.BranchClassification

  Stage 15:
    * a primitive root generates the complete unit group modulo p;
    * every exact-order-d residue is one concrete branch seed;
    * the branch index is unique in the existing 1 <= j <= d convention.
-/

import ABD.ApparitionDepth3.GlobalSynthesis
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

namespace ApparitionDepth3

/-- The unit represented by a concrete branch seed. -/
noncomputable def branchUnit
    (g p d j : Nat) (hcopG : g.Coprime p) : (ZMod p)ˣ :=
  unitMod (branchSeed g p d j) p (branchSeed_coprime hcopG)

/-- Unit-group spelling of the already proved exact-order theorem. -/
theorem branchUnit_order
    {g p d j : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j) :
    orderOf (branchUnit g p d j hcopG) = d := by
  simpa [branchUnit, OrderModIs, orderMod] using
    (branchSeed_orderModIs hcopG hprimitive hparams)

/-- The unit group modulo a prime has cardinal p-1. -/
theorem natCard_units_zmod_prime
    (p : Nat) [Fact p.Prime] :
    Nat.card ((ZMod p)ˣ) = p - 1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  exact Nat.totient_prime (Fact.out : Nat.Prime p)

/-- A primitive root in the AD3 sense generates the whole unit group. -/
theorem primitiveRoot_zpowers_eq_top
    {g p : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG) :
    Subgroup.zpowers (unitMod g p hcopG) = ⊤ := by
  let x : (ZMod p)ˣ := unitMod g p hcopG
  have hxOrder : orderOf x = p - 1 := by
    simpa [x, PrimitiveRootModP, OrderModIs, orderMod] using hprimitive
  rw [← Subgroup.card_eq_iff_eq_top]
  rw [Nat.card_zpowers, hxOrder, natCard_units_zmod_prime p]

/-- Every unit is a unique power with exponent in the canonical range
0 <= k < p-1 of the chosen primitive root.  Only existence is exposed here;
uniqueness is supplied later by power injectivity in that range. -/
theorem exists_primitiveRoot_power
    {g p : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (y : (ZMod p)ˣ) :
    ∃ k : Nat, k < p - 1 ∧
      y = (unitMod g p hcopG) ^ k := by
  let x : (ZMod p)ˣ := unitMod g p hcopG
  have hpSubPos : 0 < p - 1 :=
    Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
  have hxOrder : orderOf x = p - 1 := by
    simpa [x, PrimitiveRootModP, OrderModIs, orderMod] using hprimitive
  have hxFin : IsOfFinOrder x :=
    orderOf_ne_zero_iff.mp (by rw [hxOrder]; exact hpSubPos.ne')
  have hyMem : y ∈ Subgroup.zpowers x := by
    rw [primitiveRoot_zpowers_eq_top hcopG hprimitive]
    exact Subgroup.mem_top y
  let a : Subgroup.zpowers x := ⟨y, hyMem⟩
  let k : Fin (orderOf x) := (finEquivZPowers hxFin).symm a
  have hkPow : x ^ (k : Nat) = y :=
    pow_finEquivZPowers_symm_apply hxFin a
  refine ⟨k, ?_, hkPow.symm⟩
  simpa only [hxOrder] using k.isLt

--d = 1 の分岐
theorem branchUnit_complete_of_d_eq_one
    {g p d : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (y : (ZMod p)ˣ)
    (hyOrder : orderOf y = d)
    (hdOne : d = 1) :
    ∃ j : Nat, BranchIndex d j ∧
      y = branchUnit g p d j hcopG := by
  let x : (ZMod p)ˣ := unitMod g p hcopG
  let n : Nat := p - 1
  have hxOrder : orderOf x = n := by
    simpa [x, n, PrimitiveRootModP, OrderModIs, orderMod] using hprimitive
  refine ⟨1, ?_, ?_⟩
  · simp [BranchIndex, hdOne]
  · have hyOrderOne : orderOf y = 1 := by
      calc
        orderOf y = d := hyOrder
        _ = 1 := hdOne
    have hyOne : y = 1 :=
      orderOf_eq_one_iff.mp hyOrderOne
    have hxPow : x ^ n = 1 := by
      rw [← hxOrder]
      exact pow_orderOf_eq_one x
    calc
      y = 1 := hyOne
      _ = x ^ n := hxPow.symm
      _ = branchUnit g p d 1 hcopG := by
        rw [hdOne]
        unfold branchUnit
        rw [unitMod_branchSeed hcopG]
        simp [branchExponent, x, n]

/-- Unit-level completeness of the concrete branch formula. -/
theorem branchUnit_complete
    {g p d : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hdvd : d ∣ p - 1)
    (hdPos : 0 < d)
    (y : (ZMod p)ˣ)
    (hyOrder : orderOf y = d) :
    ∃ j : Nat, BranchIndex d j ∧ y = branchUnit g p d j hcopG := by
  let x : (ZMod p)ˣ := unitMod g p hcopG
  let n : Nat := p - 1
  let h : Nat := n / d
  have hnPos : 0 < n := by
    dsimp [n]
    exact Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
  have hxOrder : orderOf x = n := by
    simpa [x, n, PrimitiveRootModP, OrderModIs, orderMod] using hprimitive
  rcases exists_primitiveRoot_power hcopG hprimitive y with
    ⟨k, hkLt, hyPow⟩
  by_cases hdOne : d = 1
  · exact branchUnit_complete_of_d_eq_one
      hcopG hprimitive y hyOrder hdOne
  · --have hdGt : 1 < d := lt_of_le_of_ne hdPos hdOne.symm
    have hxFin : IsOfFinOrder x :=
      orderOf_ne_zero_iff.mp (by rw [hxOrder]; exact hnPos.ne')
    have hyPowOne : y ^ d = 1 := by
      rw [← hyOrder]
      exact pow_orderOf_eq_one y
    have hxPowOne : x ^ (k * d) = 1 := by
      rw [pow_mul, ← hyPow]
      exact hyPowOne
    have hnDvd : n ∣ k * d := by
      rw [← hxOrder]
      exact orderOf_dvd_of_pow_eq_one hxPowOne
    have hnEq : h * d = n := by
      dsimp [h]
      exact Nat.div_mul_cancel hdvd
    have hhdDvd : h * d ∣ k * d := by
      rw [hnEq]
      exact hnDvd
    have hhDvdK : h ∣ k :=
      (Nat.mul_dvd_mul_iff_right hdPos).mp hhdDvd
    let j : Nat := k / h
    have hkEq : k = h * j := by
      calc
        k = (k / h) * h := (Nat.div_mul_cancel hhDvdK).symm
        _ = h * j := by simp [j, Nat.mul_comm]
    have hhPos : 0 < h := by
      by_contra hh
      have hh0 : h = 0 := Nat.eq_zero_of_not_pos hh
      rw [hh0, zero_mul] at hnEq
      omega
    have hkPos : 0 < k := by
      by_contra hk
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
      have hyOne : y = 1 := by simpa [hk0] using hyPow
      have : orderOf y = 1 := by rw [hyOne, orderOf_one]
      omega
    have hjPos : 0 < j := by
      by_contra hj
      have hj0 : j = 0 := Nat.eq_zero_of_not_pos hj
      rw [hj0, mul_zero] at hkEq
      omega
    have hjLt : j < d := by
      apply (Nat.mul_lt_mul_left hhPos).mp
      rw [← hkEq, hnEq]
      simpa only [n] using hkLt
    let z : (ZMod p)ˣ := x ^ h
    have hzOrder : orderOf z = d := by
      have hxNe : orderOf x ≠ 0 := by rw [hxOrder]; exact hnPos.ne'
      have hz := orderOf_pow_orderOf_div (x := x) (n := d) hxNe (by
        simpa only [hxOrder, n] using hdvd)
      simpa only [z, h, hxOrder, n] using hz
    have hyZ : y = z ^ j := by
      calc
        y = x ^ k := hyPow
        _ = x ^ (h * j) := by rw [hkEq]
        _ = z ^ j := by simp [z, pow_mul]
    have hOrderPow : orderOf (z ^ j) = d := by
      rw [← hyZ]
      exact hyOrder
    have hdivGcd : d / Nat.gcd d j = d := by
      have hformula := orderOf_pow' z hjPos.ne'
      rw [hOrderPow, hzOrder] at hformula
      exact hformula.symm
    have hgDvd : Nat.gcd d j ∣ d := Nat.gcd_dvd_left d j
    have hmulGcd : d * Nat.gcd d j = d := by
      have hcancel := Nat.div_mul_cancel hgDvd
      rw [hdivGcd] at hcancel
      exact hcancel
    have hgcd : Nat.gcd d j = 1 := by
      apply Nat.eq_of_mul_eq_mul_left hdPos
      simpa using hmulGcd
    have hjCop : Nat.Coprime j d := by
      change Nat.gcd j d = 1
      rw [Nat.gcd_comm]
      exact hgcd
    refine ⟨j, ⟨Nat.one_le_iff_ne_zero.mpr hjPos.ne',
      Nat.le_of_lt hjLt, hjCop⟩, ?_⟩
    calc
      y = x ^ k := hyPow
      _ = x ^ (h * j) := by rw [hkEq]
      _ = branchUnit g p d j hcopG := by
        unfold branchUnit
        rw [unitMod_branchSeed hcopG]
        simp [branchExponent, x, h, n]

/-- Distinct canonical branch indices give distinct exact-order units. -/
theorem branchUnit_injective
    {g p d j₁ j₂ : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hdvd : d ∣ p - 1)
    (hdPos : 0 < d)
    (hj₁ : BranchIndex d j₁)
    (hj₂ : BranchIndex d j₂)
    (heq : branchUnit g p d j₁ hcopG =
      branchUnit g p d j₂ hcopG) :
    j₁ = j₂ := by
  by_cases hdOne : d = 1
  · subst d
    simp [BranchIndex] at hj₁ hj₂
    omega
  · --ave hdGt : 1 < d := lt_of_le_of_ne hdPos hdOne.symm
    have hj₁Lt : j₁ < d := by
      apply lt_of_le_of_ne hj₁.2.1
      intro hEq
      have hself : Nat.Coprime d d := by simpa [hEq] using hj₁.2.2
      have : d = 1 := by simpa [Nat.Coprime] using hself
      exact hdOne this
    have hj₂Lt : j₂ < d := by
      apply lt_of_le_of_ne hj₂.2.1
      intro hEq
      have hself : Nat.Coprime d d := by simpa [hEq] using hj₂.2.2
      have : d = 1 := by simpa [Nat.Coprime] using hself
      exact hdOne this
    let x : (ZMod p)ˣ := unitMod g p hcopG
    let n : Nat := p - 1
    let h : Nat := n / d
    have hnPos : 0 < n := by
      dsimp [n]
      exact Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
    have hxOrder : orderOf x = n := by
      simpa [x, n, PrimitiveRootModP, OrderModIs, orderMod] using hprimitive
    have hxFin : IsOfFinOrder x :=
      orderOf_ne_zero_iff.mp (by rw [hxOrder]; exact hnPos.ne')
    have hnEq : h * d = n := by
      dsimp [h]
      exact Nat.div_mul_cancel hdvd
    have hhPos : 0 < h := by
      by_contra hh
      have hh0 : h = 0 := Nat.eq_zero_of_not_pos hh
      rw [hh0, zero_mul] at hnEq
      omega
    have he₁Lt : h * j₁ < n := by
      rw [← hnEq]
      exact (Nat.mul_lt_mul_left hhPos).2 hj₁Lt
    have he₂Lt : h * j₂ < n := by
      rw [← hnEq]
      exact (Nat.mul_lt_mul_left hhPos).2 hj₂Lt
    have hpows : x ^ (h * j₁) = x ^ (h * j₂) := by
      unfold branchUnit at heq
      rw [unitMod_branchSeed hcopG, unitMod_branchSeed hcopG] at heq
      simpa [branchExponent, x, h, n] using heq
    have hmods := (hxFin.pow_inj_mod).mp hpows
    rw [hxOrder, Nat.mod_eq_of_lt he₁Lt, Nat.mod_eq_of_lt he₂Lt] at hmods
    exact Nat.eq_of_mul_eq_mul_left hhPos hmods

/-- Exact-order units are in bijection with the existing branch-index subtype. -/
theorem existsUnique_branchIndex_for_unit
    {g p d : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hdvd : d ∣ p - 1)
    (hdPos : 0 < d)
    (y : (ZMod p)ˣ)
    (hyOrder : orderOf y = d) :
    ∃! j : {j : Nat // BranchIndex d j},
      y = branchUnit g p d j hcopG := by
  rcases branchUnit_complete hcopG hprimitive hdvd hdPos y hyOrder with
    ⟨j, hj, hy⟩
  refine ⟨⟨j, hj⟩, hy, ?_⟩
  intro j' hy'
  apply Subtype.ext
  exact branchUnit_injective hcopG hprimitive hdvd hdPos
    j'.property hj (hy'.symm.trans hy)

/-- Natural-base spelling of completeness: every residue with exact order d is
one and only one concrete branch seed. -/
theorem existsUnique_branchIndex_for_residue
    {g p d ell : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hdvd : d ∣ p - 1)
    (hdPos : 0 < d)
    (hcopEll : ell.Coprime p)
    (horderEll : OrderModIs ell p d hcopEll) :
    ∃! j : {j : Nat // BranchIndex d j},
      (ell : ZMod p) = (branchSeed g p d j : ZMod p) := by
  let y : (ZMod p)ˣ := unitMod ell p hcopEll
  have hyOrder : orderOf y = d := by
    simpa [y, OrderModIs, orderMod] using horderEll
  rcases existsUnique_branchIndex_for_unit
      hcopG hprimitive hdvd hdPos y hyOrder with
    ⟨j, hj, hjUnique⟩
  refine ⟨j, ?_, ?_⟩
  · have hcoe := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hj
    simpa [y, branchUnit, coe_unitMod] using hcoe
  · intro j' hj'
    apply hjUnique
    apply Units.ext
    simpa [y, branchUnit, coe_unitMod] using hj'

end ApparitionDepth3
