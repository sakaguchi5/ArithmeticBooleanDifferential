import ABD.BQD.Calculus.Mirror
import ABD.BQD.Calculus.Addition

namespace ABD
namespace BQD

/-- A small BQD system combining one additive comparison and mirror comparisons.

This is still independent of ABC.  The fields `A`, `B`, and `C` are merely
three active sets over the same universe.  Later layers may interpret them as
bit-active sets of integers satisfying `a + b = c`, or as other data. -/
structure AddMirrorSystem (α : Type u) [DecidableEq α] where
  U : Finset α
  A : Finset α
  B : Finset α
  C : Finset α
  hA : A ⊆ U
  hB : B ⊆ U
  hC : C ⊆ U
  mirror : Mirror α U

namespace AddMirrorSystem

variable {α : Type u} [DecidableEq α]

/-- The additive BQD comparing the first two active sets. -/
def additive (S : AddMirrorSystem α) : Decomp α where
  U := S.U
  L := S.A
  R := S.B
  hL := S.hA
  hR := S.hB

/-- Mirror BQD for `A`. -/
def mirrorA (S : AddMirrorSystem α) : Decomp α :=
  S.mirror.pair S.A S.hA

/-- Mirror BQD for `B`. -/
def mirrorB (S : AddMirrorSystem α) : Decomp α :=
  S.mirror.pair S.B S.hB

/-- Mirror BQD for `C`. -/
def mirrorC (S : AddMirrorSystem α) : Decomp α :=
  S.mirror.pair S.C S.hC

@[simp] theorem additive_left (S : AddMirrorSystem α) :
    S.additive.L = S.A := rfl

@[simp] theorem additive_right (S : AddMirrorSystem α) :
    S.additive.R = S.B := rfl

@[simp] theorem additive_universe (S : AddMirrorSystem α) :
    S.additive.U = S.U := rfl

end AddMirrorSystem
end BQD
end ABD
