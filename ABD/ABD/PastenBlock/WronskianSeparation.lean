import ABD.ABD.PastenBlock.DerivativeRestriction
import ABD.ABD.PastenBlock.Wronskian

namespace ABD

/--
The Wronskian linear form after forgetting the `c`-block entirely.

It takes only an `a`-block tangent and a `b`-block tangent.  This is the
coordinate-level object behind the statement that Pasten's Wronskian degeneracy
is an `S_a ⊕ S_b` condition and has no dependence on the `S_c` coordinates.
-/
def ABCTriple.restrictedABWronskian
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) : ℤ :=
  (T.a : ℤ) * formalDeriv T.supportB xB T.b -
    (T.b : ℤ) * formalDeriv T.supportA xA T.a

/-- The full block Wronskian is exactly the Wronskian of the restricted
`a`- and `b`-blocks. -/
theorem ABCTriple.blockWronskian_eq_restrictedAB
    (T : ABCTriple) (x : Tangent T.support) :
    T.blockWronskian x =
      T.restrictedABWronskian (T.restrictA x) (T.restrictB x) := by
  unfold ABCTriple.blockWronskian ABCTriple.restrictedABWronskian
  rw [T.derivB_eq_formalDeriv_restrictB]
  rw [T.derivA_eq_formalDeriv_restrictA]

/-- Pasten nondegeneracy can be read purely from the restricted `a`- and
`b`-blocks. -/
theorem ABCTriple.pastenNondegenerate_iff_restrictedABWronskian_ne_zero
    (T : ABCTriple) (x : Tangent T.support) :
    T.PastenNondegenerate x ↔
      T.restrictedABWronskian (T.restrictA x) (T.restrictB x) ≠ 0 := by
  rw [T.pastenNondegenerate_iff_blockWronskian_ne_zero]
  rw [T.blockWronskian_eq_restrictedAB]

/-- If two full tangent vectors agree on the `a`- and `b`-blocks, then their
Pasten Wronskians are equal.  In particular, changing only the `c`-block cannot
change the Wronskian. -/
theorem ABCTriple.blockWronskian_congr_restrictAB
    (T : ABCTriple) (x y : Tangent T.support)
    (hA : T.restrictA x = T.restrictA y)
    (hB : T.restrictB x = T.restrictB y) :
    T.blockWronskian x = T.blockWronskian y := by
  rw [T.blockWronskian_eq_restrictedAB x]
  rw [T.blockWronskian_eq_restrictedAB y]
  rw [hA, hB]

/-- The actual Pasten nondegeneracy predicate is invariant under changing the
`c`-block while keeping the `a`- and `b`-blocks fixed. -/
theorem ABCTriple.pastenNondegenerate_congr_restrictAB
    (T : ABCTriple) (x y : Tangent T.support)
    (hA : T.restrictA x = T.restrictA y)
    (hB : T.restrictB x = T.restrictB y) :
    T.PastenNondegenerate x ↔ T.PastenNondegenerate y := by
  rw [T.pastenNondegenerate_iff_blockWronskian_ne_zero]
  rw [T.pastenNondegenerate_iff_blockWronskian_ne_zero]
  have hW : T.blockWronskian x = T.blockWronskian y :=
    T.blockWronskian_congr_restrictAB x y hA hB
  constructor
  · intro hx hy0
    exact hx (by
      rw [hW]
      exact hy0)
  · intro hy hx0
    exact hy (by
      rw [← hW]
      exact hx0)

/-- The `S_a ⊕ S_b` Wronskian-degenerate hyperplane, represented at this stage
as the kernel equation of the restricted `a/b` Wronskian form. -/
def ABCTriple.ABWronskianDegenerate
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) : Prop :=
  T.restrictedABWronskian xA xB = 0

/-- The complementary nondegenerate condition on the `S_a ⊕ S_b` side. -/
def ABCTriple.ABWronskianNondegenerate
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) : Prop :=
  T.restrictedABWronskian xA xB ≠ 0

@[simp]
theorem ABCTriple.abWronskianNondegenerate_iff_not_degenerate
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) :
    T.ABWronskianNondegenerate xA xB ↔
      ¬ T.ABWronskianDegenerate xA xB := by
  unfold ABCTriple.ABWronskianNondegenerate ABCTriple.ABWronskianDegenerate
  exact Iff.rfl

/-- Full Pasten nondegeneracy is exactly the nondegenerate condition on the
restricted `S_a ⊕ S_b` Wronskian side. -/
theorem ABCTriple.pastenNondegenerate_iff_abWronskianNondegenerate
    (T : ABCTriple) (x : Tangent T.support) :
    T.PastenNondegenerate x ↔
      T.ABWronskianNondegenerate (T.restrictA x) (T.restrictB x) := by
  rw [T.pastenNondegenerate_iff_restrictedABWronskian_ne_zero]
  rfl

end ABD
