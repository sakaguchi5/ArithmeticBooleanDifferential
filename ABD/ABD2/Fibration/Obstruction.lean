import ABD.ABD2.Fibration.Fiber

namespace ABD2
namespace ABCTriple

/-- Base obstruction: every compatible base point lies in the Wronskian kernel. -/
def BaseObstruction (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  T.BadSeed P

@[simp]
theorem baseObstruction_iff_badSeed
    (T : ABCTriple) (P : T.CImageProfile) :
    T.BaseObstruction P ↔ T.BadSeed P := by
  rfl

/-- Failure of the base obstruction is existence of a good base point. -/
theorem not_baseObstruction_iff_hasGoodBasePoint
    (T : ABCTriple) (P : T.CImageProfile) :
    ¬ T.BaseObstruction P ↔ T.HasGoodBasePoint P := by
  exact (T.hasGoodBasePoint_iff_not_BadSeed P).symm

/-- The qualitative fibration problem: a good base point exists and every
compatible base point has a nonempty C-fiber. -/
def QualitativeFibrationSolved (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  T.HasGoodBasePoint P ∧ T.FiberNonemptyForBase P

/-- A solved qualitative fibration produces a strict candidate. -/
theorem hasStrictCandidate_of_qualitativeFibrationSolved
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.QualitativeFibrationSolved P) :
    T.HasStrictCandidate := by
  rcases h with ⟨hbase, hfiber⟩
  have hseed : T.HasGoodABSeed P :=
    (T.hasGoodBasePoint_iff_hasGoodABSeed P).1 hbase
  have hlift : T.HasCLiftForCompatibleSeeds P :=
    (T.fiberNonemptyForBase_iff_hasCLiftForCompatibleSeeds P).1 hfiber
  exact T.hasStrictCandidate_of_nonzero_compatible_seed P hlift hseed

end ABCTriple
end ABD2
