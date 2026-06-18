import ABD.ABD2.Differential.All
import Mathlib.Data.Nat.GCD.Basic

namespace ABD2

/-- ABD2 triple.  The support is not stored; it is reconstructed as the Boolean
union of the prime supports of `a`, `b`, and `c`. -/
structure ABCTriple where
  a : ℕ
  b : ℕ
  c : ℕ
  add_eq : a + b = c

namespace ABCTriple

/-- The `a`-support block. -/
def supportA (T : ABCTriple) : Finset ℕ :=
  PrimeSupport T.a

/-- The `b`-support block. -/
def supportB (T : ABCTriple) : Finset ℕ :=
  PrimeSupport T.b

/-- The `c`-support block. -/
def supportC (T : ABCTriple) : Finset ℕ :=
  PrimeSupport T.c

/-- Full Pasten support. -/
def support (T : ABCTriple) : Finset ℕ :=
  T.supportA ∪ T.supportB ∪ T.supportC

/-- The primitive hypothesis, kept explicit so ABD2 does not hide the arithmetic
step behind the Boolean mask layer. -/
def Primitive (T : ABCTriple) : Prop :=
  Nat.Coprime T.a T.b

/-- The tangent module attached to the full support of the triple. -/
abbrev FullTangent (T : ABCTriple) : Type :=
  Tangent T.support

/-- The three support masks associated to a triple. -/
def maskA (T : ABCTriple) (x : T.FullTangent) : T.FullTangent :=
  supportMask T.support T.supportA x

def maskB (T : ABCTriple) (x : T.FullTangent) : T.FullTangent :=
  supportMask T.support T.supportB x

def maskC (T : ABCTriple) (x : T.FullTangent) : T.FullTangent :=
  supportMask T.support T.supportC x

@[simp]
theorem maskA_apply (T : ABCTriple) (x : T.FullTangent) :
    T.maskA x = supportMask T.support T.supportA x := by
  rfl

@[simp]
theorem maskB_apply (T : ABCTriple) (x : T.FullTangent) :
    T.maskB x = supportMask T.support T.supportB x := by
  rfl

@[simp]
theorem maskC_apply (T : ABCTriple) (x : T.FullTangent) :
    T.maskC x = supportMask T.support T.supportC x := by
  rfl

end ABCTriple
end ABD2
