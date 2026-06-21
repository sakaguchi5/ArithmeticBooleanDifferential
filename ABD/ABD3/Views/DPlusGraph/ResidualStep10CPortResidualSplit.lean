import ABD.ABD3.Views.DPlusGraph.ResidualStep9DirectedResidual

namespace ABD3

namespace ABCData

/-- A-side residual is high against the C-port `p`. -/
def AResidualHighAgainstCPort
    (T : ABCData) (_P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  LeftSyncResidualRejectedBy R G.gA (T.CPortCoeffNat p)

/-- C-side residual is high against A at the C-port `p`. -/
def CResidualHighAgainstA
    (T : ABCData) (_P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  RightSyncResidualRejectedBy R G.gA (T.CPortCoeffNat p)

/-- B-side residual is high against the C-port `p`. -/
def BResidualHighAgainstCPort
    (T : ABCData) (_P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  LeftSyncResidualRejectedBy R G.gB (T.CPortCoeffNat p)

/-- C-side residual is high against B at the C-port `p`. -/
def CResidualHighAgainstB
    (T : ABCData) (_P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  RightSyncResidualRejectedBy R G.gB (T.CPortCoeffNat p)

/-- Directed residual split for the A-C-port edge. -/
def ACPortDirectedResidualHigh
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  T.AResidualHighAgainstCPort P G R p ∨ T.CResidualHighAgainstA P G R p

/-- Directed residual split for the B-C-port edge. -/
def BCPortDirectedResidualHigh
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  T.BResidualHighAgainstCPort P G R p ∨ T.CResidualHighAgainstB P G R p

/-- A rejected A-C-port edge splits into an A-side or C-side residual obstruction. -/
theorem acPortDirectedResidualHigh_of_syncRejectedBy
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ)
    (h : SyncRejectedBy R G.gA (T.CPortCoeffNat p)) :
    T.ACPortDirectedResidualHigh P G R p := by
  unfold ACPortDirectedResidualHigh AResidualHighAgainstCPort CResidualHighAgainstA
  exact directedSyncRejectedBy_of_syncRejectedBy h

/-- A rejected B-C-port edge splits into a B-side or C-side residual obstruction. -/
theorem bcPortDirectedResidualHigh_of_syncRejectedBy
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ)
    (h : SyncRejectedBy R G.gB (T.CPortCoeffNat p)) :
    T.BCPortDirectedResidualHigh P G R p := by
  unfold BCPortDirectedResidualHigh BResidualHighAgainstCPort CResidualHighAgainstB
  exact directedSyncRejectedBy_of_syncRejectedBy h

/-- A pointwise unabsorbed C-port has directed residual splits on both A-C and B-C. -/
def CPortDirectedResidualSplitAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  p ∈ T.CSurplusPorts P ∧
    T.ACPortDirectedResidualHigh P G R p ∧
    T.BCPortDirectedResidualHigh P G R p

/-- Unabsorbed C-port data gives the Step B directed residual split. -/
theorem cPortDirectedResidualSplitAt_of_unabsorbed
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) {p : ℕ}
    (h : T.CPortUnabsorbedAt P G R p) :
    T.CPortDirectedResidualSplitAt P G R p := by
  unfold CPortDirectedResidualSplitAt
  refine ⟨h.1, ?_, ?_⟩
  · exact T.acPortDirectedResidualHigh_of_syncRejectedBy P G R p h.2.1
  · exact T.bcPortDirectedResidualHigh_of_syncRejectedBy P G R p h.2.2

/-- Rejected-edge normal form gives the Step B directed residual split at every
positive C-surplus port. -/
theorem cPortDirectedResidualSplitAt_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.RejectedEdgeNormalForm P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortDirectedResidualSplitAt P G R p := by
  exact T.cPortDirectedResidualSplitAt_of_unabsorbed P G R
    (T.cPortUnabsorbedAt_of_rejectedEdgeNormalForm P G R h hp)

/-- No accepted arithmetic edge gives the Step B directed residual split at every
positive C-surplus port. -/
theorem cPortDirectedResidualSplitAt_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.NoAcceptedArithmeticEdge P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortDirectedResidualSplitAt P G R p := by
  have hnf : T.RejectedEdgeNormalForm P G R :=
    T.rejectedEdgeNormalForm_of_noAcceptedArithmeticEdge P G R h
  exact T.cPortDirectedResidualSplitAt_of_rejectedEdgeNormalForm P G R hnf hp

/-- The C-side residual is high against both A and B at the C-port `p`. -/
def CPortCResidualHighAgainstBoth
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  T.CResidualHighAgainstA P G R p ∧ T.CResidualHighAgainstB P G R p

/-- Some active A/B-side residual is high against the C-port `p`. -/
def CPortActiveResidualHighAgainstC
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  T.AResidualHighAgainstCPort P G R p ∨ T.BResidualHighAgainstCPort P G R p

/-- Step B orientation dichotomy: after splitting the A-C and B-C rejections,
either the C-port residual is high against both active sides, or at least one
active-side residual is high against the C-port. -/
def CPortResidualOrientationDichotomy
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  T.CPortCResidualHighAgainstBoth P G R p ∨
    T.CPortActiveResidualHighAgainstC P G R p

/-- The Step B split collapses to the useful C-residual-vs-active-residual
dichotomy. -/
theorem cPortResidualOrientationDichotomy_of_split
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) {p : ℕ}
    (h : T.CPortDirectedResidualSplitAt P G R p) :
    T.CPortResidualOrientationDichotomy P G R p := by
  unfold CPortDirectedResidualSplitAt at h
  rcases h with ⟨_hp, hac, hbc⟩
  rcases hac with hA | hCA
  · unfold CPortResidualOrientationDichotomy CPortActiveResidualHighAgainstC
    exact Or.inr (Or.inl hA)
  · rcases hbc with hB | hCB
    · unfold CPortResidualOrientationDichotomy CPortActiveResidualHighAgainstC
      exact Or.inr (Or.inr hB)
    · unfold CPortResidualOrientationDichotomy CPortCResidualHighAgainstBoth
      exact Or.inl ⟨hCA, hCB⟩

/-- A pointwise unabsorbed C-port yields the orientation dichotomy. -/
theorem cPortResidualOrientationDichotomy_of_unabsorbed
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) {p : ℕ}
    (h : T.CPortUnabsorbedAt P G R p) :
    T.CPortResidualOrientationDichotomy P G R p := by
  exact T.cPortResidualOrientationDichotomy_of_split P G R
    (T.cPortDirectedResidualSplitAt_of_unabsorbed P G R h)

/-- Rejected-edge normal form yields the orientation dichotomy at every positive
C-surplus port. -/
theorem cPortResidualOrientationDichotomy_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ}
    (h : T.RejectedEdgeNormalForm P G R)
    (hp : p ∈ T.CSurplusPorts P) :
    T.CPortResidualOrientationDichotomy P G R p := by
  exact T.cPortResidualOrientationDichotomy_of_split P G R
    (T.cPortDirectedResidualSplitAt_of_rejectedEdgeNormalForm P G R h hp)

end ABCData

end ABD3
