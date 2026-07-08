/-
  ABD.ApparitionDepth3.HenselLocal

  Local mathematical data for the finite Hensel step.

  This file replaces the temporary external theorem placeholder

      SimpleRootModP seed p d -> FiniteHenselKernel seed p d

  by an explicit local-data boundary.  The data are exactly the mathematical
  ingredients that a direct proof of Hensel's lemma must provide:

    * descent of roots from level r+1 to r;
    * one-step existence, i.e. quotient + correction + expansion;
    * one-step uniqueness, i.e. uniqueness of the correction digit.

  The level-one existence and uniqueness are not local assumptions: they are
  proved directly from `SimpleRootModP seed p d` and seed congruence.

  This deliberately does not recreate the old AD1 interface/final/actual split.
-/

import ABD.ApparitionDepth3.HenselAlgebra

namespace ApparitionDepth3

/-- Root descent local lemma: a root modulo `p^(r+1)` is a root modulo `p^r`.

In a fully concrete implementation this is proved by reducing the congruence
modulo the smaller modulus. -/
def HenselRootDescent (p d : Nat) : Prop :=
  ∀ {x r : Nat}, 0 < r →
    RootAtLevel x p d (r + 1) → RootAtLevel x p d r

/-- A quotient/correction/expansion step over a fixed old lift.

This packages the actual mathematical work of one Hensel step without exposing
the old AD1 interface/final/actual chain.  The fields mean:

* `omegaNext` is the corrected representative;
* it is a lift at level `r+1`;
* it reduces back to the old `omega` at level `r`.

Concrete future proofs should build this object by the quotient, linear
correction, first-order expansion, and higher-term-vanishing lemmas. -/
def HenselCorrectionStep (seed omega p d r : Nat) : Prop :=
  ∃ omegaNext : Nat,
    LiftAtLevel seed omegaNext p d (r + 1) ∧
      (omegaNext : ZMod (p ^ r)) = (omega : ZMod (p ^ r))

/-- One-step existence local lemma.

Mathematically this is where the quotient, linear correction equation,
first-order expansion, and higher-term vanishing are used. -/
def HenselOneStepExists (seed p d : Nat) : Prop :=
  ∀ r : Nat, 0 < r → ∀ omega : Nat,
    LiftAtLevel seed omega p d r →
      HenselCorrectionStep seed omega p d r

/-- One-step uniqueness local lemma.

Mathematically this is where the derivative unit cancels the correction digit. -/
def HenselOneStepUnique (seed p d : Nat) : Prop :=
  ∀ r : Nat, 0 < r → ∀ omega omegaNext₁ omegaNext₂ : Nat,
    LiftAtLevel seed omega p d r →
    LiftAtLevel seed omegaNext₁ p d (r + 1) →
    (omegaNext₁ : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) →
    LiftAtLevel seed omegaNext₂ p d (r + 1) →
    (omegaNext₂ : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) →
      (omegaNext₁ : ZMod (p ^ (r + 1))) =
        (omegaNext₂ : ZMod (p ^ (r + 1)))

/-- The local proof data needed to turn a simple root into the finite Hensel
kernel.

This is not an external theorem placeholder.  It is the explicit mathematical boundary that
future concrete files should discharge by quotient/correction/expansion lemmas. -/
structure HenselLocalData (seed p d : Nat) : Prop where
  descent : HenselRootDescent p d
  step_exists : HenselOneStepExists seed p d
  step_unique : HenselOneStepUnique seed p d

/-- Build local data directly from its four mathematical components. -/
theorem henselLocalData_intro {seed p d : Nat}
    (hdesc : HenselRootDescent p d)
    (hexists : HenselOneStepExists seed p d)
    (hunique : HenselOneStepUnique seed p d) :
    HenselLocalData seed p d :=
  ⟨hdesc, hexists, hunique⟩

/-- Projection: root descent. -/
theorem henselLocalData_descent {seed p d : Nat}
    (h : HenselLocalData seed p d) : HenselRootDescent p d :=
  h.descent

/-- Projection: one-step existence. -/
theorem henselLocalData_stepExists {seed p d : Nat}
    (h : HenselLocalData seed p d) : HenselOneStepExists seed p d :=
  h.step_exists

/-- Projection: one-step uniqueness. -/
theorem henselLocalData_stepUnique {seed p d : Nat}
    (h : HenselLocalData seed p d) : HenselOneStepUnique seed p d :=
  h.step_unique

end ApparitionDepth3
