/-
  ABD.ApparitionDepth3.CyclotomicDepth

  Concentration of the whole p^r-depth of ell^d - 1 in the d-th
  cyclotomic factor when the residue order modulo p is exactly d.
-/

import ABD.ApparitionDepth3.PrimitiveDivisor
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

namespace ApparitionDepth3

open Polynomial

/-- Evaluation of the d-th cyclotomic polynomial at precision p^r. -/
noncomputable def cyclotomicEvalAtLevel (ell p d r : Nat) : ZMod (p ^ r) :=
  Polynomial.eval (ell : ZMod (p ^ r))
    (Polynomial.cyclotomic d (ZMod (p ^ r)))

/-- The d-th cyclotomic factor vanishes at precision p^r. -/
def CyclotomicAtLevel (ell p d r : Nat) : Prop :=
  cyclotomicEvalAtLevel ell p d r = 0

/-- The ordinary integer value Phi_d(ell). -/
noncomputable def CyclotomicValue (d ell : Nat) : Int :=
  Polynomial.eval (ell : Int) (Polynomial.cyclotomic d Int)

/-- Cyclotomic evaluation commutes with reduction from p^r to p. -/
theorem cyclotomicEval_reduce
    {ell p d r : Nat}
    (hdiv : p ∣ p ^ r) :
    ZMod.cast (cyclotomicEvalAtLevel ell p d r) =
      Polynomial.eval (ell : ZMod p)
        (Polynomial.cyclotomic d (ZMod p)) := by
  let red : ZMod (p ^ r) →+* ZMod p := ZMod.castHom hdiv (ZMod p)
  change red
      (Polynomial.eval (ell : ZMod (p ^ r))
        (Polynomial.cyclotomic d (ZMod (p ^ r)))) = _
  simpa only [red, ZMod.castHom_apply, ZMod.cast_natCast hdiv] using
    (Polynomial.cyclotomic.eval_apply
      (ell : ZMod (p ^ r)) d red).symm

/-- A proper cyclotomic factor cannot vanish modulo p when ell has exact
multiplicative order d modulo p. -/
theorem cyclotomicEval_modP_ne_zero_of_properDivisor
    {ell p d e : Nat} [Fact p.Prime]
    {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hdPos : 0 < d)
    (he : e ∈ Nat.properDivisors d) :
    Polynomial.eval (ell : ZMod p)
      (Polynomial.cyclotomic e (ZMod p)) ≠ 0 := by
  intro hzero
  have heDvd : e ∣ d := (Nat.mem_properDivisors.mp he).1
  have heLt : e < d := (Nat.mem_properDivisors.mp he).2
  have hePos : 0 < e := Nat.pos_of_dvd_of_pos heDvd hdPos
  have hrootCycl :
      (Polynomial.cyclotomic e (ZMod p)).IsRoot (ell : ZMod p) := hzero
  have hrootPowPoly :
      (Polynomial.X ^ e - 1 : (ZMod p)[X]).IsRoot (ell : ZMod p) := by
    rw [Polynomial.IsRoot.def,
      ← Polynomial.prod_cyclotomic_eq_X_pow_sub_one hePos (ZMod p),
      ← Nat.cons_self_properDivisors hePos.ne', Finset.prod_cons,
      Polynomial.eval_mul, hzero, zero_mul]
  have hpow : ((ell : ZMod p) ^ e = 1) := by
    unfold Polynomial.IsRoot at hrootPowPoly
    have hz : (ell : ZMod p) ^ e - 1 = 0 := by simpa using hrootPowPoly
    exact sub_eq_zero.mp hz
  have hunitPow : UnitPowOneAt ell p e hcop :=
    (unitPowOneAt_iff_residuePowOne hcop).mpr hpow
  have hdDvdE : d ∣ e := orderModIs_dvd_of_unitPowOneAt hord hunitPow
  have hdLe : d ≤ e := Nat.le_of_dvd hePos hdDvdE
  exact (not_lt_of_ge hdLe) heLt

/-- Every proper cyclotomic factor is a unit at every positive prime-power
precision. -/
theorem cyclotomicEval_isUnit_of_properDivisor
    {ell p d e r : Nat} [Fact p.Prime]
    {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hdPos : 0 < d)
    (hrPos : 0 < r)
    (he : e ∈ Nat.properDivisors d) :
    IsUnit
      (Polynomial.eval (ell : ZMod (p ^ r))
        (Polynomial.cyclotomic e (ZMod (p ^ r)))) := by
  have hdiv : p ∣ p ^ r := by
    cases r with
    | zero => exact False.elim ((Nat.not_lt_zero 0) hrPos)
    | succ k =>
        rw [pow_succ]
        exact dvd_mul_left p (p ^ k)
  have hredEq := cyclotomicEval_reduce (ell := ell) (p := p) (d := e) hdiv
  have hredNe :=
    cyclotomicEval_modP_ne_zero_of_properDivisor hord hdPos he
  have hredUnit :
      IsUnit
        (ZMod.cast
          (Polynomial.eval (ell : ZMod (p ^ r))
            (Polynomial.cyclotomic e (ZMod (p ^ r)))) : ZMod p) := by
    change IsUnit ((cyclotomicEvalAtLevel ell p e r).cast : ZMod p)
    rw [hredEq]
    exact isUnit_iff_ne_zero.mpr hredNe
  exact isUnit_primePower_of_reduction_isUnit hrPos hredUnit

/-- The product of all proper cyclotomic factors is a unit modulo p^r. -/
theorem properCyclotomicProduct_isUnit
    {ell p d r : Nat} [Fact p.Prime]
    {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hdPos : 0 < d)
    (hrPos : 0 < r) :
    IsUnit
      (∏ e ∈ Nat.properDivisors d,
        Polynomial.eval (ell : ZMod (p ^ r))
          (Polynomial.cyclotomic e (ZMod (p ^ r)))) := by
  classical
  let U : (ZMod (p ^ r))ˣ :=
    Finset.prod (Nat.properDivisors d).attach
      (fun e =>
        (cyclotomicEval_isUnit_of_properDivisor
          hord hdPos hrPos e.property).unit)
  refine ⟨U, ?_⟩
  rw [← Finset.prod_attach]
  simp [U]

/-- Exact order modulo p and the root equation modulo p^r force the complete
p^r-depth into Phi_d(ell). -/
theorem cyclotomicAtLevel_of_exactOrder_rootAtLevel
    {ell p d r : Nat} [Fact p.Prime]
    {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hdPos : 0 < d)
    (hrPos : 0 < r)
    (hroot : RootAtLevel ell p d r) :
    CyclotomicAtLevel ell p d r := by
  classical
  let R := ZMod (p ^ r)
  let B : R :=
    ∏ e ∈ Nat.properDivisors d,
      Polynomial.eval (ell : R) (Polynomial.cyclotomic e R)
  have hBUnit : IsUnit B := by
    dsimp [B, R]
    exact properCyclotomicProduct_isUnit hord hdPos hrPos
  have hpoly := Polynomial.prod_cyclotomic_eq_X_pow_sub_one hdPos R
  rw [← Nat.cons_self_properDivisors hdPos.ne', Finset.prod_cons] at hpoly
  have heval := congrArg (Polynomial.eval (ell : R)) hpoly
  have hrootEq := hroot
  unfold RootAtLevel at hrootEq
  have hprod : cyclotomicEvalAtLevel ell p d r * B = 0 := by
    unfold cyclotomicEvalAtLevel
    dsimp [B, R] at heval ⊢
    simp only [Polynomial.eval_mul, Polynomial.eval_prod] at heval
    simpa [hrootEq] using heval
  let u : Rˣ := hBUnit.unit
  have hmul : cyclotomicEvalAtLevel ell p d r * (u : R) = 0 := by
    rw [hBUnit.unit_spec]
    exact hprod
  unfold CyclotomicAtLevel
  calc
    cyclotomicEvalAtLevel ell p d r =
        cyclotomicEvalAtLevel ell p d r *
          ((u : R) * ((u⁻¹ : Rˣ) : R)) := by simp
    _ = (cyclotomicEvalAtLevel ell p d r * (u : R)) *
          ((u⁻¹ : Rˣ) : R) := by rw [mul_assoc]
    _ = 0 := by rw [hmul, zero_mul]

/-- Vanishing at precision p^r is exactly integer divisibility of Phi_d(ell)
by p^r. -/
theorem cyclotomicAtLevel_iff_int_dvd
    {ell p d r : Nat} :
    CyclotomicAtLevel ell p d r ↔
      ((p ^ r : Nat) : Int) ∣ CyclotomicValue d ell := by
  unfold CyclotomicAtLevel cyclotomicEvalAtLevel CyclotomicValue
  have hcast :
      (ell : ZMod (p ^ r)) =
        Int.castRingHom (ZMod (p ^ r)) (ell : Int) := by simp
  rw [hcast, Polynomial.cyclotomic.eval_apply]
  simpa using
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (Polynomial.eval (ell : Int) (Polynomial.cyclotomic d Int)) (p ^ r))

/-- Teichmuller-class version of cyclotomic depth concentration. -/
theorem teichmullerClass_cyclotomicAtLevel
    {g p d j omega r ell : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (hlift : TeichmullerLiftAtLevel g p d j omega r)
    (hellClass : (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)))
    (hellPos : 0 < ell) :
    CyclotomicAtLevel ell p d r := by
  have hclass :=
    teichmullerClassResult hcopG hprimitive hparams hrPos hlift hellClass hellPos
  exact cyclotomicAtLevel_of_exactOrder_rootAtLevel
    hclass.exactOrder (branchParams_d_pos hparams) hrPos hclass.rootAtLevel

/-- Integer divisibility form of the Teichmuller-class cyclotomic theorem. -/
theorem teichmullerClass_cyclotomicDepth
    {g p d j omega r ell : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (hlift : TeichmullerLiftAtLevel g p d j omega r)
    (hellClass : (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)))
    (hellPos : 0 < ell) :
    ((p ^ r : Nat) : Int) ∣ CyclotomicValue d ell :=
  cyclotomicAtLevel_iff_int_dvd.mp
    (teichmullerClass_cyclotomicAtLevel
      hcopG hprimitive hparams hrPos hlift hellClass hellPos)

end ApparitionDepth3
