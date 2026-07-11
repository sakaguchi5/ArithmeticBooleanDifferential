/-
  ABD.ApparitionDepth3.FiniteSynthesis

  Finite-level synthesis of concrete Teichmuller generation, exact apparition,
  primitive-divisor status, cyclotomic depth, and the unique next carry digit.
-/

import ABD.ApparitionDepth3.HenselCarry

namespace ApparitionDepth3

/-- Carry data attached to one concrete finite representative.

This is data, rather than a proposition: it contains the actual correction
residue in `ZMod p`, together with proofs characterizing that residue. -/
structure FiniteCarryResult
    (seed omega p d r : Nat) where
  correction : ZMod p
  nextDigit : ∀ t : Nat,
    RootAtLevel (correctedRepresentative omega t p r) p d (r + 1) ↔
      (t : ZMod p) = correction
  zeroCarry :
    RootAtLevel omega p d (r + 1) ↔ correction = 0
  errorZero :
    correction = 0 ↔ HenselErrorDigit omega p d r = 0

/-- Propositional wrapper used when only existence of concrete carry data is
needed. -/
def HasFiniteCarryResult
    (seed omega p d r : Nat) : Prop :=
  Nonempty (FiniteCarryResult seed omega p d r)

/-- Full finite-level public data for a positive integer `ell` in the same
`p^r`-class as a generated representative `omega`. -/
structure FiniteApparitionSynthesisResult
    (ell omega g p d j r : Nat) where
  lift : TeichmullerLiftAtLevel g p d j omega r
  sameClass : (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r))
  basePositive : 0 < ell
  classResult : TeichmullerClassResult ell p d r
  primitive : PrimitivePrimeDivisor ell p d
  cyclotomicAtLevel : CyclotomicAtLevel ell p d r
  cyclotomicDepth : ((p ^ r : Nat) : Int) ∣ CyclotomicValue d ell
  carry : FiniteCarryResult (branchSeed g p d j) omega p d r

/-- Propositional wrapper for existence of the complete finite synthesis data. -/
def HasFiniteApparitionSynthesisResult
    (ell omega g p d j r : Nat) : Prop :=
  Nonempty (FiniteApparitionSynthesisResult ell omega g p d j r)

/-- Concrete carry data for a finite Teichmuller lift. -/
noncomputable def finiteCarryResult_of_teichmullerLift
    {g p d j omega r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (hlift : TeichmullerLiftAtLevel g p d j omega r) :
    FiniteCarryResult (branchSeed g p d j) omega p d r := by
  let hsimple : SimpleRootModP (branchSeed g p d j) p d :=
    branchSeed_simpleRoot hcopG hprimitive hparams
  let hunit : IsUnit (derivativeAt omega p d) :=
    derivativeUnit_of_seedCongr hsimple hlift.1
  let c : ZMod p := HenselCorrectionDigit omega p d r hunit
  refine
    { correction := c
      nextDigit := ?_
      zeroCarry := ?_
      errorZero := ?_ }
  · intro t
    dsimp [c, hunit, hsimple]
    exact rootAtNextLevel_iff_digit_eq_canonical hsimple hrPos hlift
  · dsimp [c, hunit, hsimple]
    exact rootAtNextLevel_iff_correctionDigit_zero hsimple hrPos hlift
  · dsimp [c, hunit]
    exact correctionDigit_eq_zero_iff_errorDigit_eq_zero hunit

/-- Finite synthesis for every positive base in a concrete Teichmuller class. -/
noncomputable def finiteTeichmullerApparitionSynthesis
    {g p d j omega r ell : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (hlift : TeichmullerLiftAtLevel g p d j omega r)
    (hellClass : (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)))
    (hellPos : 0 < ell) :
    FiniteApparitionSynthesisResult ell omega g p d j r := by
  have hclass :=
    teichmullerClassResult hcopG hprimitive hparams hrPos hlift hellClass hellPos
  have hprimitiveDiv : PrimitivePrimeDivisor ell p d :=
    teichmullerClass_primitivePrimeDivisor
      hcopG hprimitive hparams hrPos hlift hellClass hellPos
  have hcycl : CyclotomicAtLevel ell p d r :=
    teichmullerClass_cyclotomicAtLevel
      hcopG hprimitive hparams hrPos hlift hellClass hellPos
  have hcyclDepth : ((p ^ r : Nat) : Int) ∣ CyclotomicValue d ell :=
    cyclotomicAtLevel_iff_int_dvd.mp hcycl
  have hcarry : FiniteCarryResult (branchSeed g p d j) omega p d r :=
    finiteCarryResult_of_teichmullerLift
      hcopG hprimitive hparams hrPos hlift
  exact
    { lift := hlift
      sameClass := hellClass
      basePositive := hellPos
      classResult := hclass
      primitive := hprimitiveDiv
      cyclotomicAtLevel := hcycl
      cyclotomicDepth := hcyclDepth
      carry := hcarry }

/-- Canonical-representative form of the finite synthesis data. -/
noncomputable def finiteTeichmullerLiftSynthesis
    {g p d j omega r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (hlift : TeichmullerLiftAtLevel g p d j omega r) :
    FiniteApparitionSynthesisResult omega omega g p d j r := by
  have hsimple := branchSeed_simpleRoot hcopG hprimitive hparams
  have homegaPos : 0 < omega :=
    liftRepresentative_pos_of_simpleRoot hsimple hlift
  exact finiteTeichmullerApparitionSynthesis
    hcopG hprimitive hparams hrPos hlift rfl homegaPos

/-- Existence form: branch parameters produce a canonical finite representative
carrying every stage 4-9 conclusion. -/
theorem exists_finiteTeichmullerApparitionSynthesis
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    ∃ omega : Nat,
      HasFiniteApparitionSynthesisResult omega omega g p d j r := by
  rcases existsUniqueTeichmullerLiftAtLevel
      hcopG hprimitive hparams hrPos with ⟨omega, hlift, _hunique⟩
  exact ⟨omega, ⟨
    finiteTeichmullerLiftSynthesis
      hcopG hprimitive hparams hrPos hlift⟩⟩

/-- The compact finite synthesis consequence most useful to later p-adic/Witt
files. -/
theorem exists_finiteLift_with_primitive_cyclotomic_carry
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    ∃ omega : Nat,
      TeichmullerLiftAtLevel g p d j omega r ∧
      FirstAppearsWithDepthAtLeast omega p d r ∧
      PrimitivePrimeDivisor omega p d ∧
      ((p ^ r : Nat) : Int) ∣ CyclotomicValue d omega ∧
      HasFiniteCarryResult (branchSeed g p d j) omega p d r := by
  rcases exists_finiteTeichmullerApparitionSynthesis
      hcopG hprimitive hparams hrPos with ⟨omega, ⟨hsyn⟩⟩
  exact ⟨omega, hsyn.lift, hsyn.classResult.firstWithDepth,
    hsyn.primitive, hsyn.cyclotomicDepth, ⟨hsyn.carry⟩⟩

end ApparitionDepth3
