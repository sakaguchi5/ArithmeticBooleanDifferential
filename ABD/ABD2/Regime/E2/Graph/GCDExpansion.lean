import ABD.ABD2.Regime.E2.Graph.Desynchronization

namespace ABD2
namespace ABCTriple

/-- A coarse gcd/lcm synchronization scale for two positive-image generators.

This is the numerical shell for the later arithmetic analysis.  If `x` and `y`
share a large gcd, the scale is small; if they are poorly synchronized, the scale
is large. -/
def SyncScaleNat (x y : ℕ) : ℕ :=
  max (x / Nat.gcd x y) (y / Nat.gcd x y)

/-- A pair of scalar image generators is accepted by a regime if its `SyncScaleNat`
fits under some regime-accepted integer bound. -/
def SyncAcceptedBy
    (T : ABCTriple) (R : T.BoundRegime) (x y : ℕ) : Prop :=
  ∃ B : ℤ,
    (SyncScaleNat x y : ℤ) ≤ B ∧ R.accepts B

/-- Rejection of a gcd/lcm synchronization pair. -/
def SyncRejectedBy
    (T : ABCTriple) (R : T.BoundRegime) (x y : ℕ) : Prop :=
  ¬ T.SyncAcceptedBy R x y

/-- Rejected synchronization unfolded as a universal high-cost condition. -/
theorem syncRejectedBy_iff_forall_rejects_bound
    (T : ABCTriple) (R : T.BoundRegime) (x y : ℕ) :
    T.SyncRejectedBy R x y ↔
      ∀ B : ℤ, R.accepts B → ¬ ((SyncScaleNat x y : ℤ) ≤ B) := by
  constructor
  · intro h B hB hle
    exact h ⟨B, hle, hB⟩
  · intro h hacc
    rcases hacc with ⟨B, hle, hB⟩
    exact h B hB hle

/-- Pairwise gcd/lcm desynchronization for one C-side candidate scalar `alpha`.

This is the Step-4 arithmetic normal form: A/B are desynchronized, and the
C-candidate scalar is desynchronized from both A and B. -/
def PairwiseGCDDesynchronizationAt
    (T : ABCTriple) (R : T.BoundRegime) (gA gB alpha : ℕ) : Prop :=
  T.SyncRejectedBy R gA gB ∧
    T.SyncRejectedBy R gA alpha ∧
      T.SyncRejectedBy R gB alpha

/-- The A-B part of pairwise gcd desynchronization. -/
theorem abSyncRejected_of_pairwiseGCDDesynchronizationAt
    (T : ABCTriple) (R : T.BoundRegime) {gA gB alpha : ℕ}
    (h : T.PairwiseGCDDesynchronizationAt R gA gB alpha) :
    T.SyncRejectedBy R gA gB := by
  exact h.1

/-- The A-C part of pairwise gcd desynchronization. -/
theorem acSyncRejected_of_pairwiseGCDDesynchronizationAt
    (T : ABCTriple) (R : T.BoundRegime) {gA gB alpha : ℕ}
    (h : T.PairwiseGCDDesynchronizationAt R gA gB alpha) :
    T.SyncRejectedBy R gA alpha := by
  exact h.2.1

/-- The B-C part of pairwise gcd desynchronization. -/
theorem bcSyncRejected_of_pairwiseGCDDesynchronizationAt
    (T : ABCTriple) (R : T.BoundRegime) {gA gB alpha : ℕ}
    (h : T.PairwiseGCDDesynchronizationAt R gA gB alpha) :
    T.SyncRejectedBy R gB alpha := by
  exact h.2.2

/-- Constructor for pairwise gcd desynchronization from the three rejected edges. -/
theorem pairwiseGCDDesynchronizationAt_of_rejected_edges
    (T : ABCTriple) (R : T.BoundRegime) {gA gB alpha : ℕ}
    (hAB : T.SyncRejectedBy R gA gB)
    (hAC : T.SyncRejectedBy R gA alpha)
    (hBC : T.SyncRejectedBy R gB alpha) :
    T.PairwiseGCDDesynchronizationAt R gA gB alpha := by
  exact ⟨hAB, hAC, hBC⟩

end ABCTriple
end ABD2
