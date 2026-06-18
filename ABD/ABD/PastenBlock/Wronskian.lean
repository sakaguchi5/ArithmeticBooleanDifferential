import ABD.ABD.PastenBlock.Derivative

namespace ABD

/-- The Pasten Wronskian written using only the `a`- and `b`-block derivative values. -/
def ABCTriple.blockWronskian (T : ABCTriple) (x : Tangent T.support) : ℤ :=
  (T.a : ℤ) * T.derivB x - (T.b : ℤ) * T.derivA x

@[simp]
theorem ABCTriple.blockWronskian_eq_wronskian
    (T : ABCTriple) (x : Tangent T.support) :
    T.blockWronskian x = T.wronskian x := by
  rfl

/-- Pasten nondegeneracy is exactly nonvanishing of the block Wronskian. -/
theorem ABCTriple.pastenNondegenerate_iff_blockWronskian_ne_zero
    (T : ABCTriple) (x : Tangent T.support) :
    T.PastenNondegenerate x ↔ T.blockWronskian x ≠ 0 := by
  simp [
    ABCTriple.PastenNondegenerate,
    ABD.PastenNondegenerate,
    ABCTriple.blockWronskian,
    ABCTriple.derivA,
    ABCTriple.derivB,
    WronskianOn
  ]

/-- A strict Pasten candidate has nonzero block Wronskian. -/
theorem StrictPastenCandidate.blockWronskian_ne_zero
    {T : ABCTriple} (h : StrictPastenCandidate T) :
    T.blockWronskian h.x ≠ 0 :=
  (T.pastenNondegenerate_iff_blockWronskian_ne_zero h.x).1 h.nondegenerate

/-- A small strict Pasten candidate has nonzero block Wronskian. -/
theorem SmallStrictPastenCandidate.blockWronskian_ne_zero
    {T : ABCTriple} {B : ℤ} (h : SmallStrictPastenCandidate T B) :
    T.blockWronskian h.x ≠ 0 :=
  (T.pastenNondegenerate_iff_blockWronskian_ne_zero h.x).1 h.nondegenerate

end ABD
