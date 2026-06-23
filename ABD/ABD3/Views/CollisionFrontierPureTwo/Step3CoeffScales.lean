import ABD.ABD3.Views.CollisionFrontierPureTwo.Step2Equation

namespace ABD3
namespace ABCData
namespace PureTwoPowerNormalForm

variable {T : ABCData} {P : PowerData}

/-- The expected A-side coefficient generator in the pure model:
`u * p^(u-1)`. -/
def pureGA (F : PureTwoPowerNormalForm T P) : ℕ :=
  F.u * F.p ^ (F.u - 1)

/-- The expected B-side coefficient generator in the pure model:
`v * q^(v-1)`. -/
def pureGB (F : PureTwoPowerNormalForm T P) : ℕ :=
  F.v * F.q ^ (F.v - 1)

/-- The expected C-side coefficient generator in the pure model:
`w * 2^(w-1)`. -/
def pureGC (F : PureTwoPowerNormalForm T P) : ℕ :=
  F.w * 2 ^ (F.w - 1)

/-- The pure-model A/B arithmetic synchronization generators. -/
def pureSyncGenerators (F : PureTwoPowerNormalForm T P) :
    ArithmeticSyncGenerators :=
  { gA := F.pureGA, gB := F.pureGB }

@[simp] theorem pureSyncGenerators_gA (F : PureTwoPowerNormalForm T P) :
    F.pureSyncGenerators.gA = F.pureGA := rfl

@[simp] theorem pureSyncGenerators_gB (F : PureTwoPowerNormalForm T P) :
    F.pureSyncGenerators.gB = F.pureGB := rfl

/-- Optional bridge facts connecting the pure generators to the actual coefficient
scales already defined in ABD3.

This is a fact package rather than a theorem because the arithmetic proof of
`coeffOf (p^u) p = u*p^(u-1)` is reusable but somewhat heavier.  Keeping it as a
separate package lets the sync-graph normal form be developed immediately. -/
structure PureCoeffScaleFacts (F : PureTwoPowerNormalForm T P) where
  hA : T.coeffAbsA F.p = F.pureGA
  hB : T.coeffAbsB F.q = F.pureGB
  hC : T.CPortCoeffNat 2 = F.pureGC

/-- A named proposition for the eventual concrete coefficient-scale proof. -/
def HasPureCoeffScaleFacts (F : PureTwoPowerNormalForm T P) : Prop :=
  Nonempty (PureCoeffScaleFacts F)

theorem coeffAbsA_eq_pureGA_of_facts
    (F : PureTwoPowerNormalForm T P)
    (H : PureCoeffScaleFacts F) :
    T.coeffAbsA F.p = F.pureGA :=
  H.hA

theorem coeffAbsB_eq_pureGB_of_facts
    (F : PureTwoPowerNormalForm T P)
    (H : PureCoeffScaleFacts F) :
    T.coeffAbsB F.q = F.pureGB :=
  H.hB

theorem cPortCoeffNat_two_eq_pureGC_of_facts
    (F : PureTwoPowerNormalForm T P)
    (H : PureCoeffScaleFacts F) :
    T.CPortCoeffNat 2 = F.pureGC :=
  H.hC

end PureTwoPowerNormalForm
end ABCData
end ABD3
