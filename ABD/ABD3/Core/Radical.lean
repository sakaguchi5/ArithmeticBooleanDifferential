import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ABD.ABD3.Core.Support

namespace ABD3

open Finset

/-- Multiplicative radical measure on a Boolean support: product of its primes.

This is the point where a Boolean support object becomes an arithmetic weight. -/
def radOfSupport (S : Support) : ℕ :=
  S.prod (fun p => p)

namespace ABCData

/-- A-side squarefree radical, defined from the A-side support. -/
def radA (T : ABCData) : ℕ :=
  radOfSupport T.supportA

/-- B-side squarefree radical, defined from the B-side support. -/
def radB (T : ABCData) : ℕ :=
  radOfSupport T.supportB

/-- C-side squarefree radical, defined from the C-side support. -/
def radC (T : ABCData) : ℕ :=
  radOfSupport T.supportC

/-- Full squarefree radical of the triple, defined from the full Boolean support. -/
def radABC (T : ABCData) : ℕ :=
  radOfSupport T.supportABC

/-- The block product that becomes `radABC` under block-disjointness. -/
def blockRadicalProduct (T : ABCData) : ℕ :=
  T.radA * T.radB * T.radC

/-- View asserting that the full radical splits as the three block radicals. -/
def BlockRadicalProductView (T : ABCData) : Prop :=
  T.radABC = T.blockRadicalProduct

@[simp] theorem radA_def (T : ABCData) : T.radA = radOfSupport T.supportA := rfl
@[simp] theorem radB_def (T : ABCData) : T.radB = radOfSupport T.supportB := rfl
@[simp] theorem radC_def (T : ABCData) : T.radC = radOfSupport T.supportC := rfl
@[simp] theorem radABC_def (T : ABCData) : T.radABC = radOfSupport T.supportABC := rfl

/-- Expand the full radical to the union of block supports. -/
theorem radABC_eq_radOf_blockUnion (T : ABCData) :
    T.radABC = radOfSupport (T.supportA ∪ T.supportB ∪ T.supportC) := by
  rfl

end ABCData
end ABD3
