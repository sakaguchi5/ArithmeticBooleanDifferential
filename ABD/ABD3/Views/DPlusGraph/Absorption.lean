import ABD.ABD3.Views.DPlusGraph.CPort

namespace ABD3

/-- ABD3-only arithmetic generators for the A/B scalar-image sides.

This deliberately avoids importing ABD2.  Later bridge files may instantiate
`gA` and `gB` using actual gcd generators of the A/B coefficient ideals. -/
structure ArithmeticSyncGenerators where
  gA : ℕ
  gB : ℕ

namespace ABCData

/-- The C-port coefficient scale `|v_p(C) * C / p|`, as a natural number.

ABD3 already has `coeffC : ℕ → ℤ`; this is the natural scale used by the
pure gcd/lcm synchronization graph. -/
def CPortCoeffNat (T : ABCData) (p : ℕ) : ℕ :=
  Int.natAbs (T.coeffC p)

/-- gcd/lcm synchronization scale between two natural generators.

Large value means that the two generators share little gcd and must pay a large
lcm multiplier to synchronize. -/
def SyncScaleNat (x y : ℕ) : ℕ :=
  max (x / Nat.gcd x y) (y / Nat.gcd x y)

/-- The pair `(x,y)` is accepted by a bound `R` when its synchronization scale is
at most `R`. -/
def SyncAcceptedBy (R x y : ℕ) : Prop :=
  SyncScaleNat x y ≤ R

/-- The pair `(x,y)` is rejected by a bound `R` when its synchronization scale is
larger than `R`. -/
def SyncRejectedBy (R x y : ℕ) : Prop :=
  R < SyncScaleNat x y

/-- A rejected edge is not accepted at the same bound. -/
theorem not_syncAcceptedBy_of_syncRejectedBy
    {R x y : ℕ} (h : SyncRejectedBy R x y) :
    ¬ SyncAcceptedBy R x y := by
  intro ha
  unfold SyncAcceptedBy SyncRejectedBy at *
  omega

/-- A positive C-port is absorbed by A if the A/C-port synchronization is cheap. -/
def CPortAbsorbedByA
    (T : ABCData) (_P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  SyncAcceptedBy R G.gA (T.CPortCoeffNat p)

/-- A positive C-port is absorbed by B if the B/C-port synchronization is cheap. -/
def CPortAbsorbedByB
    (T : ABCData) (_P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  SyncAcceptedBy R G.gB (T.CPortCoeffNat p)

/-- A positive C-port is unabsorbed when neither A nor B accepts it. -/
def CPortUnabsorbedAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) (p : ℕ) : Prop :=
  p ∈ T.CSurplusPorts P ∧
    SyncRejectedBy R G.gA (T.CPortCoeffNat p) ∧
    SyncRejectedBy R G.gB (T.CPortCoeffNat p)

/-- The A-B edge is rejected. -/
def ABEdgeRejected
    (_T : ABCData) (_P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  SyncRejectedBy R G.gA G.gB

/-- Low absorption of C-port mass: every positive C-surplus port is rejected by
both A and B. -/
def CPortAbsorptionLow
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ∀ p, p ∈ T.CSurplusPorts P → T.CPortUnabsorbedAt P G R p

/-- ABD3 arithmetic accepted edge: either A-B is cheap, or some positive C-port is
cheaply absorbed by A or by B. -/
def HasAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  SyncAcceptedBy R G.gA G.gB ∨
    ∃ p, p ∈ T.CSurplusPorts P ∧
      (T.CPortAbsorbedByA P G R p ∨ T.CPortAbsorbedByB P G R p)

/-- No accepted arithmetic edge: the A-B edge is rejected and all positive C-ports
are rejected by both A and B. -/
def NoAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ABEdgeRejected P G R ∧ T.CPortAbsorptionLow P G R

/-- No accepted arithmetic edge implies low C-port absorption. -/
theorem cPortAbsorptionLow_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.NoAcceptedArithmeticEdge P G R) :
    T.CPortAbsorptionLow P G R :=
  h.2

/-- No accepted arithmetic edge implies A-B rejection. -/
theorem abEdgeRejected_of_noAcceptedArithmeticEdge
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.NoAcceptedArithmeticEdge P G R) :
    T.ABEdgeRejected P G R :=
  h.1

/-- Low absorption gives pointwise unabsorbed ports. -/
theorem cPortUnabsorbedAt_of_absorptionLow
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hlow : T.CPortAbsorptionLow P G R)
    {p : ℕ} (hp : p ∈ T.CSurplusPorts P) :
    T.CPortUnabsorbedAt P G R p :=
  hlow p hp

/-- Pointwise unabsorbed ports are not accepted by A. -/
theorem not_cPortAbsorbedByA_of_unabsorbed
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ} (h : T.CPortUnabsorbedAt P G R p) :
    ¬ T.CPortAbsorbedByA P G R p := by
  exact not_syncAcceptedBy_of_syncRejectedBy h.2.1

/-- Pointwise unabsorbed ports are not accepted by B. -/
theorem not_cPortAbsorbedByB_of_unabsorbed
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    {p : ℕ} (h : T.CPortUnabsorbedAt P G R p) :
    ¬ T.CPortAbsorbedByB P G R p := by
  exact not_syncAcceptedBy_of_syncRejectedBy h.2.2

end ABCData

end ABD3
