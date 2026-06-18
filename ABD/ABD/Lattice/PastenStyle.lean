import ABD.ABD.Lattice.PastenLeibniz

namespace ABD

/--
A fully packaged Pasten-style derivative object in the ABD language.

Compared with `PastenCandidate`, this structure stores the Leibniz facts explicitly.
Those facts are not assumptions when converting from `PastenCandidate`: they are supplied
by the theoremized formal-derivative construction on the triple support.
-/
structure PastenStyleDerivative (T : ABCTriple) where
  x : Tangent T.support
  additive : AdditiveOn T.support x T.a T.b T.c
  leibniz_ab : LeibnizOn T.support x T.a T.b
  leibniz_ac : LeibnizOn T.support x T.a T.c
  leibniz_bc : LeibnizOn T.support x T.b T.c
  nondegenerate : Nondegenerate T.support x

/--
A small Pasten-style derivative object in the ABD language.

The smallness field is still the current coordinatewise `SmallTangent`; this is the
place where later geometry-of-numbers bounds can be refined without changing the
lower differential construction.
-/
structure SmallPastenStyleDerivative (T : ABCTriple) (B : ℤ) where
  x : Tangent T.support
  additive : AdditiveOn T.support x T.a T.b T.c
  leibniz_ab : LeibnizOn T.support x T.a T.b
  leibniz_ac : LeibnizOn T.support x T.a T.c
  leibniz_bc : LeibnizOn T.support x T.b T.c
  nondegenerate : Nondegenerate T.support x
  small : SmallTangent T.support x B

/-- Forget the smallness field from a small Pasten-style derivative. -/
def SmallPastenStyleDerivative.toPastenStyleDerivative
    {T : ABCTriple} {B : ℤ}
    (h : SmallPastenStyleDerivative T B) : PastenStyleDerivative T where
  x := h.x
  additive := h.additive
  leibniz_ab := h.leibniz_ab
  leibniz_ac := h.leibniz_ac
  leibniz_bc := h.leibniz_bc
  nondegenerate := h.nondegenerate

/--
A `PastenCandidate` becomes a fully packaged Pasten-style derivative because the
Leibniz rules on the triple support are now theoremized.
-/
def PastenCandidate.toPastenStyleDerivative
    {T : ABCTriple}
    (h : PastenCandidate T) : PastenStyleDerivative T where
  x := h.x
  additive := h.additive
  leibniz_ab := h.leibniz_ab
  leibniz_ac := h.leibniz_ac
  leibniz_bc := h.leibniz_bc
  nondegenerate := h.nondegenerate

/-- A `SmallPastenCandidate` becomes a small fully packaged Pasten-style derivative. -/
def SmallPastenCandidate.toSmallPastenStyleDerivative
    {T : ABCTriple} {B : ℤ}
    (h : SmallPastenCandidate T B) : SmallPastenStyleDerivative T B where
  x := h.x
  additive := h.additive
  leibniz_ab := h.leibniz_ab
  leibniz_ac := h.leibniz_ac
  leibniz_bc := h.leibniz_bc
  nondegenerate := h.nondegenerate
  small := h.small

/-- Forget smallness after converting a small candidate to the packaged style. -/
def SmallPastenCandidate.toPastenStyleDerivative
    {T : ABCTriple} {B : ℤ}
    (h : SmallPastenCandidate T B) : PastenStyleDerivative T :=
  (h.toSmallPastenStyleDerivative).toPastenStyleDerivative

@[simp] theorem PastenCandidate.toPastenStyleDerivative_x
    {T : ABCTriple} (h : PastenCandidate T) :
    h.toPastenStyleDerivative.x = h.x := rfl

@[simp] theorem SmallPastenCandidate.toSmallPastenStyleDerivative_x
    {T : ABCTriple} {B : ℤ} (h : SmallPastenCandidate T B) :
    h.toSmallPastenStyleDerivative.x = h.x := rfl

@[simp] theorem SmallPastenStyleDerivative.toPastenStyleDerivative_x
    {T : ABCTriple} {B : ℤ} (h : SmallPastenStyleDerivative T B) :
    h.toPastenStyleDerivative.x = h.x := rfl

end ABD
