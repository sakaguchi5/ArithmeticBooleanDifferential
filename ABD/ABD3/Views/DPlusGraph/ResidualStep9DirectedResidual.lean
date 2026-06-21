import ABD.ABD3.Views.DPlusGraph.ResidualStep8MinimalSupportBoundary

namespace ABD3

namespace ABCData

/-- The left-side residual after the common gcd has been shared. -/
def LeftSyncResidualNat (x y : ℕ) : ℕ :=
  x / Nat.gcd x y

/-- The right-side residual after the common gcd has been shared. -/
def RightSyncResidualNat (x y : ℕ) : ℕ :=
  y / Nat.gcd x y

/-- The synchronization scale is the maximum of the two directed residuals. -/
theorem syncScaleNat_eq_max_directedResiduals (x y : ℕ) :
    SyncScaleNat x y =
      max (LeftSyncResidualNat x y) (RightSyncResidualNat x y) := by
  rfl

/-- The left-side residual is too large for the bound `R`. -/
def LeftSyncResidualRejectedBy (R x y : ℕ) : Prop :=
  R < LeftSyncResidualNat x y

/-- The right-side residual is too large for the bound `R`. -/
def RightSyncResidualRejectedBy (R x y : ℕ) : Prop :=
  R < RightSyncResidualNat x y

/-- Directed rejected synchronization: at least one directed residual is too large.

This is the Step A ledger refinement of an undirected rejected edge. -/
def DirectedSyncRejectedBy (R x y : ℕ) : Prop :=
  LeftSyncResidualRejectedBy R x y ∨ RightSyncResidualRejectedBy R x y

/-- A rejected synchronization edge is exactly a directed residual rejection. -/
theorem directedSyncRejectedBy_iff_syncRejectedBy
    {R x y : ℕ} :
    DirectedSyncRejectedBy R x y ↔ SyncRejectedBy R x y := by
  constructor
  · intro h
    unfold DirectedSyncRejectedBy LeftSyncResidualRejectedBy
      RightSyncResidualRejectedBy LeftSyncResidualNat RightSyncResidualNat at h
    unfold SyncRejectedBy SyncScaleNat
    rcases h with hleft | hright
    · exact lt_of_lt_of_le hleft (le_max_left _ _)
    · exact lt_of_lt_of_le hright (le_max_right _ _)
  · intro h
    unfold SyncRejectedBy SyncScaleNat at h
    unfold DirectedSyncRejectedBy LeftSyncResidualRejectedBy
      RightSyncResidualRejectedBy LeftSyncResidualNat RightSyncResidualNat
    exact lt_max_iff.mp h

/-- Extract directed residual data from a rejected edge. -/
theorem directedSyncRejectedBy_of_syncRejectedBy
    {R x y : ℕ} (h : SyncRejectedBy R x y) :
    DirectedSyncRejectedBy R x y := by
  exact directedSyncRejectedBy_iff_syncRejectedBy.mpr h

/-- Forget directed residual data back to ordinary rejected synchronization. -/
theorem syncRejectedBy_of_directedSyncRejectedBy
    {R x y : ℕ} (h : DirectedSyncRejectedBy R x y) :
    SyncRejectedBy R x y := by
  exact directedSyncRejectedBy_iff_syncRejectedBy.mp h

/-- Rejection is exactly non-acceptance at the same bound. -/
theorem syncRejectedBy_iff_not_syncAcceptedBy
    {R x y : ℕ} :
    SyncRejectedBy R x y ↔ ¬ SyncAcceptedBy R x y := by
  unfold SyncRejectedBy SyncAcceptedBy
  omega

/-- The A-side residual of the A-B edge is high. -/
def AResidualHighAgainstB
    (_T : ABCData) (_P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  LeftSyncResidualRejectedBy R G.gA G.gB

/-- The B-side residual of the A-B edge is high. -/
def BResidualHighAgainstA
    (_T : ABCData) (_P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  RightSyncResidualRejectedBy R G.gA G.gB

/-- Directed residual normal form for the rejected A-B edge. -/
def ABDirectedResidualHigh
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.AResidualHighAgainstB P G R ∨ T.BResidualHighAgainstA P G R

/-- The directed A-B residual ledger is exactly the rejected A-B edge. -/
theorem abDirectedResidualHigh_iff_abEdgeRejected
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.ABDirectedResidualHigh P G R ↔ T.ABEdgeRejected P G R := by
  unfold ABDirectedResidualHigh AResidualHighAgainstB BResidualHighAgainstA
    ABEdgeRejected
  exact directedSyncRejectedBy_iff_syncRejectedBy

/-- A rejected A-B edge splits into an A-residual-high or B-residual-high case. -/
theorem abDirectedResidualHigh_of_abEdgeRejected
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ABEdgeRejected P G R) :
    T.ABDirectedResidualHigh P G R := by
  exact (T.abDirectedResidualHigh_iff_abEdgeRejected P G R).mpr h

/-- Directed A-B residual data extracted from the rejected-edge normal form. -/
theorem abDirectedResidualHigh_of_rejectedEdgeNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.RejectedEdgeNormalForm P G R) :
    T.ABDirectedResidualHigh P G R := by
  exact T.abDirectedResidualHigh_of_abEdgeRejected P G R h.1

/-- Directed A-B residual data extracted directly from no-accepted-edge. -/
theorem abDirectedResidualHigh_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.NoAcceptedArithmeticEdge P G R) :
    T.ABDirectedResidualHigh P G R := by
  exact T.abDirectedResidualHigh_of_abEdgeRejected P G R
    (T.abEdgeRejected_of_noAcceptedArithmeticEdge P G R h)

end ABCData

end ABD3
