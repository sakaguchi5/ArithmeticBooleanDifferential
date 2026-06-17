import ABD.PastenBlock.Support
import ABD.Lattice.PastenT

namespace ABD

/-- The `a`-side derivative value of a full Pasten tangent vector. -/
def ABCTriple.derivA (T : ABCTriple) (x : Tangent T.support) : ℤ :=
  formalDeriv T.support x T.a

/-- The `b`-side derivative value of a full Pasten tangent vector. -/
def ABCTriple.derivB (T : ABCTriple) (x : Tangent T.support) : ℤ :=
  formalDeriv T.support x T.b

/-- The `c`-side derivative value of a full Pasten tangent vector. -/
def ABCTriple.derivC (T : ABCTriple) (x : Tangent T.support) : ℤ :=
  formalDeriv T.support x T.c

/-- Difference form of the Pasten additive equation in block notation. -/
def ABCTriple.blockTarget (T : ABCTriple) (x : Tangent T.support) : ℤ :=
  T.derivA x + T.derivB x - T.derivC x

@[simp]
theorem ABCTriple.blockTarget_eq_additiveLinearForm
    (T : ABCTriple) (x : Tangent T.support) :
    T.blockTarget x = AdditiveLinearForm T.support x T.a T.b T.c := by
  rfl

/-- Membership in Pasten's `T(a,b)` is exactly the block additive equation. -/
theorem ABCTriple.mem_pastenT_iff_block_equation
    (T : ABCTriple) (x : Tangent T.support) :
    x ∈ PastenT T ↔ T.derivA x + T.derivB x = T.derivC x := by
  rw [mem_pastenT_iff]
  rfl

/-- Membership in Pasten's `T(a,b)` is exactly vanishing of the block target. -/
theorem ABCTriple.mem_pastenT_iff_blockTarget_zero
    (T : ABCTriple) (x : Tangent T.support) :
    x ∈ PastenT T ↔ T.blockTarget x = 0 := by
  rw [mem_pastenT_iff]
  rw [additiveOn_iff_linearForm_zero]
  rfl

end ABD
