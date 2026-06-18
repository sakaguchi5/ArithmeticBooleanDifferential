/-
Copyright (c) 2026 NOIZ. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NOIZ
-/
import ABD.ABD.Differential.TripleCandidate

namespace ABD

/--
The Pasten-style Wronskian attached to two integers and a formal derivative
candidate on a finite prime support.

For a tangent vector `x`, this is

`W_x(a,b) = a * D_x(b) - b * D_x(a)`.

This is the predicate that should drive Pasten-style nondegeneracy, not merely
coordinatewise nonzeroness of `x`.
-/
def WronskianOn (S : Finset ℕ) (x : Tangent S) (a b : ℕ) : ℤ :=
  (a : ℤ) * formalDeriv S x b - (b : ℤ) * formalDeriv S x a

/-- The actual Pasten-facing nondegeneracy predicate: the Wronskian is nonzero. -/
def PastenNondegenerate (S : Finset ℕ) (x : Tangent S) (a b : ℕ) : Prop :=
  WronskianOn S x a b ≠ 0

/-- Triple-specialized Wronskian. -/
def ABCTriple.wronskian (T : ABCTriple) (x : Tangent T.support) : ℤ :=
  WronskianOn T.support x T.a T.b

/-- Triple-specialized Pasten nondegeneracy. -/
def ABCTriple.PastenNondegenerate (T : ABCTriple) (x : Tangent T.support) : Prop :=
  ABD.PastenNondegenerate T.support x T.a T.b

@[simp]
theorem ABCTriple.wronskian_eq (T : ABCTriple) (x : Tangent T.support) :
    T.wronskian x = WronskianOn T.support x T.a T.b := by
  rfl

@[simp]
theorem ABCTriple.pastenNondegenerate_iff
    (T : ABCTriple) (x : Tangent T.support) :
    T.PastenNondegenerate x ↔ WronskianOn T.support x T.a T.b ≠ 0 := by
  rfl

/-- A convenience bridge from an evaluated Wronskian to nondegeneracy. -/
theorem pastenNondegenerate_of_wronskian_eq
    {S : Finset ℕ} {x : Tangent S} {a b : ℕ} {w : ℤ}
    (hW : WronskianOn S x a b = w) (hw : w ≠ 0) :
    PastenNondegenerate S x a b := by
  unfold PastenNondegenerate
  rw [hW]
  exact hw

end ABD
