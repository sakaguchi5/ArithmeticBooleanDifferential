/-
  ABD.ApparitionDepth3.GlobalSynthesis

  Stage 14:
    fixed-branch synthesis of finite apparition, cyclotomic depth, primitive
    divisor status, the p-adic/Witt root, the ordinary digit expansion, and the
    exact-depth branch tree.
-/

import ABD.ApparitionDepth3.PadicDigitExpansion

namespace ApparitionDepth3

/-- The complete result attached to one concrete `(g,p,d,j)` branch. -/
structure GlobalApparitionSynthesisResult
    (g p d j : Nat) [Fact p.Prime] where
  padicBridge : PadicTeichmullerBridgeResult g p d j
  digitExpansion : PadicDigitExpansionResult g p d j
  finiteAtLevel : ∀ r : Nat, 0 < r →
    FiniteApparitionSynthesisResult
      (branchPadicRepresentative g p d j r)
      (branchPadicRepresentative g p d j r)
      g p d j r
  carryAtLevel : ∀ r : Nat, 0 < r →
    PadicWittCarryBridgeResult g p d j r
  treeAtLevel : ∀ r : Nat, 0 < r →
    BranchTreeLevelResult g p d j r
  compatible : ∀ m n : Nat, m ≤ n →
    ZMod.cast (branchPadicReduction g p d j n) =
      branchPadicReduction g p d j m
  finiteAgreement : ∀ (r omega : Nat), 0 < r →
    TeichmullerLiftAtLevel g p d j omega r →
      (omega : ZMod (p ^ r)) = branchPadicReduction g p d j r

/-- Fixed-branch global synthesis. -/
noncomputable def globalApparitionSynthesis
    {g p d j : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j) :
    GlobalApparitionSynthesisResult g p d j := by
  let hpadic : PadicTeichmullerBridgeResult g p d j :=
    padicTeichmullerBridgeResult hcopG hprimitive hparams
  refine
    { padicBridge := hpadic
      digitExpansion := padicDigitExpansionResult
      finiteAtLevel := ?_
      carryAtLevel := ?_
      treeAtLevel := ?_
      compatible := ?_
      finiteAgreement := ?_ }
  · intro r hrPos
    exact finiteTeichmullerLiftSynthesis
      hcopG hprimitive hparams hrPos
      (branchPadicRepresentative_teichmullerLift
        hcopG hprimitive hparams hrPos)
  · intro r hrPos
    exact padicWittCarryBridgeResult
      hcopG hprimitive hparams hrPos
  · intro r hrPos
    exact branchTreeLevelResult
      hcopG hprimitive hparams hrPos
  · intro m n hmn
    exact branchPadicReduction_compat hmn
  · intro r omega hrPos hlift
    exact teichmullerLift_eq_branchPadicReduction
      hcopG hprimitive hparams hrPos hlift

/-- Existence spelling of the fixed-branch global theorem. -/
theorem exists_globalApparitionSynthesis
    {g p d j : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j) :
    Nonempty (GlobalApparitionSynthesisResult g p d j) :=
  ⟨globalApparitionSynthesis hcopG hprimitive hparams⟩

/-- Compact public consequence at an arbitrary positive level. -/
theorem globalSynthesis_atLevel
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    FirstAppearsWithDepthAtLeast
        (branchPadicRepresentative g p d j r) p d r ∧
      PrimitivePrimeDivisor
        (branchPadicRepresentative g p d j r) p d ∧
      ((p ^ r : Nat) : Int) ∣
        CyclotomicValue d (branchPadicRepresentative g p d j r) ∧
      ∃! t : ZMod p,
        RootAtLevel
          (branchChild (branchPadicRepresentative g p d j r) t r)
          p d (r + 1) := by
  let hglobal := globalApparitionSynthesis hcopG hprimitive hparams
  have hfinite := hglobal.finiteAtLevel r hrPos
  exact ⟨hfinite.classResult.firstWithDepth,
    hfinite.primitive,
    hfinite.cyclotomicDepth,
    existsUnique_continuingBranchChild
      hcopG hprimitive hparams hrPos⟩

end ApparitionDepth3
