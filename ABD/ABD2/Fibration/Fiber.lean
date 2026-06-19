import ABD.ABD2.Fibration.Base
import ABD.ABD2.Reduction.StrictReduction

namespace ABD2
namespace ABCTriple

/-- The C-side fiber over an AB seed: all lifts preserving the A/B masks and
absorbing the seed target on the C side. -/
def FiberOver (T : ABCTriple) (seed : T.FullTangent) : Set T.FullTangent :=
  {lift | T.HasCLift seed lift}

@[simp]
theorem mem_FiberOver_iff
    (T : ABCTriple) (seed lift : T.FullTangent) :
    lift ∈ T.FiberOver seed ↔ T.HasCLift seed lift := by
  rfl

/-- The fiber over a seed is nonempty. -/
def FiberNonempty (T : ABCTriple) (seed : T.FullTangent) : Prop :=
  ∃ lift : T.FullTangent, lift ∈ T.FiberOver seed

@[simp]
theorem fiberNonempty_iff_exists_HasCLift
    (T : ABCTriple) (seed : T.FullTangent) :
    T.FiberNonempty seed ↔ ∃ lift : T.FullTangent, T.HasCLift seed lift := by
  rfl

/-- Every compatible base point has a nonempty C-fiber. -/
def FiberNonemptyForBase (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  ∀ seed : T.FullTangent, seed ∈ T.ABBase P → T.FiberNonempty seed

/-- The fibration-language fiber-nonemptiness principle is the existing
`HasCLiftForCompatibleSeeds`. -/
theorem fiberNonemptyForBase_iff_hasCLiftForCompatibleSeeds
    (T : ABCTriple) (P : T.CImageProfile) :
    T.FiberNonemptyForBase P ↔ T.HasCLiftForCompatibleSeeds P := by
  constructor
  · intro h seed hseed
    rcases h seed hseed with ⟨lift, hlift⟩
    exact ⟨lift, hlift⟩
  · intro h seed hseed
    rcases h seed hseed with ⟨lift, hlift⟩
    exact ⟨lift, hlift⟩

end ABCTriple
end ABD2
