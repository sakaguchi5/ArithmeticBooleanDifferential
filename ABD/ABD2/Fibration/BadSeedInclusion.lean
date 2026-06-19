import ABD.ABD2.Fibration.StrictSkeleton

namespace ABD2
namespace ABCTriple

/-- Phase 2 inclusion form: the first bad-seed obstruction is exactly that the
AB-side fibration base is contained in the Wronskian-degenerate locus. -/
theorem badSeed_iff_ABBase_le_BaseWronskianKernel
    (T : ABCTriple) (P : T.CImageProfile) :
    T.BadSeed P ↔ T.ABBase P ≤ T.BaseWronskianKernel := by
  rfl

/-- Negated inclusion form of the first bad-seed obstruction. -/
theorem not_badSeed_iff_not_ABBase_le_BaseWronskianKernel
    (T : ABCTriple) (P : T.CImageProfile) :
    ¬ T.BadSeed P ↔ ¬ (T.ABBase P ≤ T.BaseWronskianKernel) := by
  constructor
  · intro hnot hle
    exact hnot ((T.badSeed_iff_ABBase_le_BaseWronskianKernel P).2 hle)
  · intro hnot hbad
    exact hnot ((T.badSeed_iff_ABBase_le_BaseWronskianKernel P).1 hbad)

/-- A good base point exists exactly when the AB base is not contained in the
Wronskian-degenerate locus. -/
theorem hasGoodBasePoint_iff_not_ABBase_le_BaseWronskianKernel
    (T : ABCTriple) (P : T.CImageProfile) :
    T.HasGoodBasePoint P ↔ ¬ (T.ABBase P ≤ T.BaseWronskianKernel) := by
  constructor
  · intro hgood hle
    have hbad : T.BadSeed P :=
      (T.badSeed_iff_ABBase_le_BaseWronskianKernel P).2 hle
    exact (T.hasGoodBasePoint_iff_not_BadSeed P).1 hgood hbad
  · intro hnotle
    apply (T.hasGoodBasePoint_iff_not_BadSeed P).2
    intro hbad
    exact hnotle ((T.badSeed_iff_ABBase_le_BaseWronskianKernel P).1 hbad)

/-- The fibration-language base obstruction is the same inclusion statement. -/
theorem baseObstruction_iff_ABBase_le_BaseWronskianKernel
    (T : ABCTriple) (P : T.CImageProfile) :
    T.BaseObstruction P ↔ T.ABBase P ≤ T.BaseWronskianKernel := by
  exact (T.baseObstruction_iff_badSeed P).trans
    (T.badSeed_iff_ABBase_le_BaseWronskianKernel P)

/-- Failure of the base obstruction is failure of the inclusion. -/
theorem not_baseObstruction_iff_not_ABBase_le_BaseWronskianKernel
    (T : ABCTriple) (P : T.CImageProfile) :
    ¬ T.BaseObstruction P ↔ ¬ (T.ABBase P ≤ T.BaseWronskianKernel) := by
  constructor
  · intro hnot hle
    have hob : T.BaseObstruction P :=
      (T.baseObstruction_iff_ABBase_le_BaseWronskianKernel P).2 hle
    exact hnot hob
  · intro hnotle hob
    exact hnotle ((T.baseObstruction_iff_ABBase_le_BaseWronskianKernel P).1 hob)

end ABCTriple
end ABD2
