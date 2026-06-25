import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step22StandardKillableRegistry

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- If the scale-unbalanced family at scale `C` is absent, then the two source
terms are balanced within the same factor `C`.

This is the integer proxy for the informal principle:

`not (one side is at least C times the other)` implies
`the two sides are within a factor C`. -/
theorem scaleBalancedBy_of_not_scaleUnbalancedBy
    (F : NormalForm T P) (K : BothOddResidualHardCore F)
    {C : ℕ} (hC : 1 < C)
    (hnot : ¬ Branch5ScaleUnbalancedBy (T := T) (P := P) C F K) :
    Branch5ScaleBalancedBy (T := T) (P := P) C F K := by
  refine ⟨hC, ?_, ?_⟩
  · have hnot_right : ¬ F.q ^ F.v * C ≤ F.p ^ F.u := by
      intro hright
      exact hnot ⟨hC, Or.inr hright⟩
    have hlt : F.p ^ F.u < F.q ^ F.v * C :=
      lt_of_not_ge hnot_right
    have hle : F.p ^ F.u ≤ F.q ^ F.v * C :=
      Nat.le_of_lt hlt
    simpa [Nat.mul_comm] using hle
  · have hnot_left : ¬ F.p ^ F.u * C ≤ F.q ^ F.v := by
      intro hleft
      exact hnot ⟨hC, Or.inl hleft⟩
    have hlt : F.q ^ F.v < F.p ^ F.u * C :=
      lt_of_not_ge hnot_left
    have hle : F.q ^ F.v ≤ F.p ^ F.u * C :=
      Nat.le_of_lt hlt
    simpa [Nat.mul_comm] using hle

/-- A candidate avoiding the standard registry avoids the scale-unbalanced part
registered inside it. -/
theorem not_scaleUnbalancedBy_of_residualAfter_standardKillableRegistry
    {B L C : ℕ} {S : Finset ℕ}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (R : BothOddResidualAfterKillable
      (T := T) (P := P)
      (StandardKillableRegistry (T := T) (P := P) B L C S) F K) :
    ¬ Branch5ScaleUnbalancedBy (T := T) (P := P) C F K := by
  intro hscale
  exact R.not_killable
    (mem_standardKillableRegistry_of_scaleUnbalanced
      (T := T) (P := P) (B := B) (L := L) (C := C) (S := S) hscale)

/-- Avoiding the standard registry gives the balanced branch at the registered
scale. -/
theorem scaleBalancedBy_of_residualAfter_standardKillableRegistry
    {B L C : ℕ} {S : Finset ℕ}
    (F : NormalForm T P) (K : BothOddResidualHardCore F)
    (hC : 1 < C)
    (R : BothOddResidualAfterKillable
      (T := T) (P := P)
      (StandardKillableRegistry (T := T) (P := P) B L C S) F K) :
    Branch5ScaleBalancedBy (T := T) (P := P) C F K :=
  scaleBalancedBy_of_not_scaleUnbalancedBy
    (T := T) (P := P) F K hC
    (not_scaleUnbalancedBy_of_residualAfter_standardKillableRegistry
      (T := T) (P := P) (B := B) (L := L) (C := C) (S := S) R)

/-- Build the balanced two-adic core automatically from a residual candidate
that avoids the standard killable registry. -/
def balancedTwoAdicDesyncCore_of_residualAfter_standardKillableRegistry
    {B L C : ℕ} {S : Finset ℕ}
    (F : NormalForm T P) (K : BothOddResidualHardCore F)
    (hC : 1 < C)
    (R : BothOddResidualAfterKillable
      (T := T) (P := P)
      (StandardKillableRegistry (T := T) (P := P) B L C S) F K) :
    BalancedTwoAdicDesyncCore
      (T := T) (P := P)
      (StandardKillableRegistry (T := T) (P := P) B L C S) C F K :=
  balancedTwoAdicDesyncCore_of_residual
    (T := T) (P := P)
    (Killable := StandardKillableRegistry (T := T) (P := P) B L C S)
    (C := C) F K R
    (scaleBalancedBy_of_residualAfter_standardKillableRegistry
      (T := T) (P := P) (B := B) (L := L) (C := C) (S := S) F K hC R)

/-- A candidate avoiding a standard registry extended by an extra family still
avoids the underlying standard registry if the extension is defined by union.

This helper is intentionally one-way: avoiding a bigger registry is stronger. -/
theorem residualAfter_standard_of_residualAfter_standardWithExtra
    {B L C : ℕ} {S : Finset ℕ}
    {Extra : Branch5Family T P}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (R : BothOddResidualAfterKillable
      (T := T) (P := P)
      (StandardKillableRegistry.withExtra
        (T := T) (P := P) B L C S Extra) F K) :
    BothOddResidualAfterKillable
      (T := T) (P := P)
      (StandardKillableRegistry (T := T) (P := P) B L C S) F K := by
  refine ⟨?_⟩
  intro hstandard
  exact R.not_killable
    (mem_standardKillableRegistry_withExtra_of_standard
      (T := T) (P := P) (B := B) (L := L) (C := C) (S := S)
      (Extra := Extra) hstandard)

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
