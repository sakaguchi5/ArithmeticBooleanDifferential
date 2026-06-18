import ABD.ABD.Examples.TwoThreeFive
import ABD.ABD.Lattice.All

namespace ABD.Examples

/-- The additive triple `2 + 3 = 5`. -/
def twoThreeFiveTriple : ABD.ABCTriple where
  a := 2
  b := 3
  c := 5
  ha_pos := by decide
  hb_pos := by decide
  hc_pos := by decide
  h_add := by decide

/-- The zero differential candidate on `2 + 3 = 5`.

This is only a wiring example: it checks that Core triples, Differential
candidates, and the Lattice/Siegel bridge compose in the intended DAG. -/
def zeroDifferentialCandidate235 : ABD.DifferentialCandidate twoThreeFiveTriple where
  x := ABD.zeroTangent twoThreeFiveTriple.support
  additive := by simp

example :
    ABD.SiegelLinearEquation twoThreeFiveTriple
      (ABD.zeroTangent twoThreeFiveTriple.support) := by
  simp [ABD.SiegelLinearEquation, ABD.AdditiveLinearForm]

/-- A simple nonzero tangent on the hand-written toy support `{2, 3, 5}`.

This is not claimed to satisfy the additive equation; it only tests the current
minimal nondegeneracy predicate. -/
def toyNonzeroTangent235 : ABD.Tangent S235 :=
  fun hp => if hp.1 = 2 then 1 else 0

example : ABD.Nondegenerate S235 toyNonzeroTangent235 := by
  refine ⟨⟨2, by simp [S235]⟩, ?_⟩
  simp [toyNonzeroTangent235]

example : ABD.LeibnizOn S235 (ABD.zeroTangent S235) 2 3 := by
  simp

end ABD.Examples
