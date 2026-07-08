/-
  ABD.ApparitionDepth3.SimpleRoot

  The only simple-root data Hensel needs for X^d - 1.
-/

import ABD.ApparitionDepth3.Branch

namespace ApparitionDepth3

/-- Formal derivative of `X^d - 1` at `x`, evaluated modulo `p`.

For `d = 0`, Lean's natural exponent `d - 1` is `0`; the intended use always
has `0 < d`. -/
def derivativeAt (x p d : Nat) : ZMod p :=
  (d : ZMod p) * (x : ZMod p) ^ (d - 1)

/-- Concrete simple-root package modulo `p`. -/
def SimpleRootModP (x p d : Nat) : Prop :=
  RootAtLevel x p d 1 ∧ IsUnit (derivativeAt x p d)

/-- Seed-level simple root. -/
def SeedSimpleRootModP (seed p d : Nat) : Prop :=
  SimpleRootModP seed p d

/-- Constructor for a simple root of `X^d - 1`. -/
theorem simpleRoot_intro {x p d : Nat}
    (hroot : RootAtLevel x p d 1)
    (hderiv : IsUnit (derivativeAt x p d)) :
    SimpleRootModP x p d :=
  ⟨hroot, hderiv⟩

theorem simpleRoot_root {x p d : Nat}
    (h : SimpleRootModP x p d) : RootAtLevel x p d 1 :=
  h.1

theorem simpleRoot_derivative_unit {x p d : Nat}
    (h : SimpleRootModP x p d) : IsUnit (derivativeAt x p d) :=
  h.2

/-- If a representative is congruent to a simple seed modulo `p`, then it is a
root modulo `p`.

The derivative-unit transport is deliberately not bundled here: for future use it
is cleaner to keep it as a separate congruence lemma when needed. -/
theorem rootAtLevel_one_of_seedSimpleRoot_of_seedCongr
    {seed omega p d : Nat}
    (hsimple : SeedSimpleRootModP seed p d)
    (hseed : BranchSeedModP seed omega p) :
    RootAtLevel omega p d 1 :=
  rootAtLevel_one_of_seedRoot_of_seedCongr (simpleRoot_root hsimple) hseed

end ApparitionDepth3
