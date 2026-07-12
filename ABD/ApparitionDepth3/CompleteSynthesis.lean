/-
  ABD.ApparitionDepth3.CompleteSynthesis

  Stage 18:
    final public theorem.  Odd primes are classified by all primitive-root
    branches; p=2 is classified by the two mod-4 branches +1 and -1.
-/

import ABD.ApparitionDepth3.TwoAdicModFour

namespace ApparitionDepth3

/-- The complete public theory.  The two cases intentionally have different
initial boundaries: mod p for odd p and mod 4 for p=2. -/
structure CompleteApparitionSynthesis where
  oddPrimeTheory :
    ∀ {g p d : Nat} [Fact p.Prime],
      p ≠ 2 →
      (hcopG : g.Coprime p) →
      PrimitiveRootModP g p hcopG →
      d ∣ p - 1 →
      0 < d →
      OddPrimeCompleteSynthesis g p d hcopG
  twoAdicTheory : TwoAdicCompleteSynthesis

/-- Final construction joining stages 1-18. -/
noncomputable def completeApparitionSynthesis : CompleteApparitionSynthesis :=
  { oddPrimeTheory := fun hpOdd hcopG hprimitive hdvd hdPos =>
      oddPrimeCompleteSynthesis hpOdd hcopG hprimitive hdvd hdPos
    twoAdicTheory := twoAdicCompleteSynthesis }

/-- Final odd-prime consequence in a compact theorem shape. -/
theorem completeOddPrimeBranchClassification
    {g p d : Nat} [Fact p.Prime]
    (hpOdd : p ≠ 2)
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hdvd : d ∣ p - 1)
    (hdPos : 0 < d) :
    (∀ j : Nat, BranchIndex d j →
      Nonempty (GlobalApparitionSynthesisResult g p d j)) ∧
    (∀ y : (ZMod p)ˣ, orderOf y = d →
      ∃! j : {j : Nat // BranchIndex d j},
        y = branchUnit g p d j hcopG) ∧
    (∀ (ell : Nat) (hcopEll : ell.Coprime p),
      OrderModIs ell p d hcopEll →
        ∃! j : {j : Nat // BranchIndex d j},
          (ell : ZMod p) = (branchSeed g p d j : ZMod p)) ∧
    (∀ (theta : ℤ_[p])
        (_hroot : theta ^ d = 1)
        (hcopTheta : (padicLevelRepresentative theta 1).Coprime p),
      OrderModIs (padicLevelRepresentative theta 1) p d hcopTheta →
        ∃! j : {j : Nat // BranchIndex d j},
          theta = branchPadicRoot g p d j) := by
  let h := oddPrimeCompleteSynthesis
    hpOdd hcopG hprimitive hdvd hdPos
  exact ⟨fun j hj => ⟨h.branchSynthesis j hj⟩,
    h.unitClassification, h.residueClassification, h.padicClassification⟩

/-- Final p=2 consequence: mod 4 separates the two roots, and they exhaust all
2-adic square roots of one. -/
theorem completeTwoAdicModFourClassification :
    Nonempty (TwoAdicBranchSynthesisResult .positive) ∧
    Nonempty (TwoAdicBranchSynthesisResult .negative) ∧
    twoAdicSeedModFour .positive ≠ twoAdicSeedModFour .negative ∧
    ∀ theta : ℤ_[2], theta ^ 2 = 1 →
      theta = twoAdicPadicRoot .positive ∨
        theta = twoAdicPadicRoot .negative := by
  let h := twoAdicCompleteSynthesis
  exact ⟨⟨h.positive⟩, ⟨h.negative⟩,
    h.distinguishedModFour, h.complete⟩

end ApparitionDepth3
