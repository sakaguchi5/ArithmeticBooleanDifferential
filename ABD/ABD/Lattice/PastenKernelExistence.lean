/-
Copyright (c) 2026 NOIZ. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NOIZ
-/
import ABD.ABD.Lattice.PastenKernel

namespace ABD

/--
A small nondegenerate point of the additive-kernel submodule attached to a triple.

This is the geometry-of-numbers facing version of a small Pasten candidate: the
point is recorded first as an element of the `Submodule`, and the extra
conditions are exactly the current nondegeneracy and smallness predicates.
-/
structure SmallNondegenerateKernelPoint (T : ABCTriple) (B : ℤ) where
  x : Tangent T.support
  mem_kernel : x ∈ TripleAdditiveKernelSubmodule T
  nondegenerate : Nondegenerate T.support x
  small : SmallTangent T.support x B

/-- Existence of a Pasten candidate for a triple, without a size bound. -/
def HasPastenCandidate (T : ABCTriple) : Prop :=
  ∃ x : Tangent T.support,
    AdditiveOn T.support x T.a T.b T.c ∧
    Nondegenerate T.support x

/-- Existence of a small Pasten candidate for a triple. -/
def HasSmallPastenCandidate (T : ABCTriple) (B : ℤ) : Prop :=
  ∃ x : Tangent T.support,
    AdditiveOn T.support x T.a T.b T.c ∧
    Nondegenerate T.support x ∧
    SmallTangent T.support x B

/-- Existence of a small nondegenerate point in the triple additive-kernel submodule. -/
def HasSmallNondegenerateKernelPoint (T : ABCTriple) (B : ℤ) : Prop :=
  ∃ x : Tangent T.support,
    x ∈ TripleAdditiveKernelSubmodule T ∧
    Nondegenerate T.support x ∧
    SmallTangent T.support x B

/-- A small Pasten candidate is a small nondegenerate kernel point. -/
def SmallPastenCandidate.toSmallNondegenerateKernelPoint
    {T : ABCTriple} {B : ℤ}
    (h : SmallPastenCandidate T B) : SmallNondegenerateKernelPoint T B where
  x := h.x
  mem_kernel := h.mem_tripleAdditiveKernelSubmodule
  nondegenerate := h.nondegenerate
  small := h.small

/-- A small nondegenerate kernel point is a small Pasten candidate. -/
def SmallNondegenerateKernelPoint.toSmallPastenCandidate
    {T : ABCTriple} {B : ℤ}
    (h : SmallNondegenerateKernelPoint T B) : SmallPastenCandidate T B where
  x := h.x
  additive := (mem_tripleAdditiveKernelSubmodule_iff T h.x).1 h.mem_kernel
  nondegenerate := h.nondegenerate
  small := h.small

/-- A small Pasten-style derivative is a small nondegenerate kernel point. -/
def SmallPastenStyleDerivative.toSmallNondegenerateKernelPoint
    {T : ABCTriple} {B : ℤ}
    (h : SmallPastenStyleDerivative T B) : SmallNondegenerateKernelPoint T B where
  x := h.x
  mem_kernel := h.mem_tripleAdditiveKernelSubmodule
  nondegenerate := h.nondegenerate
  small := h.small

/-- A small Pasten candidate gives the corresponding existence predicate. -/
theorem SmallPastenCandidate.hasSmallNondegenerateKernelPoint
    {T : ABCTriple} {B : ℤ}
    (h : SmallPastenCandidate T B) :
    HasSmallNondegenerateKernelPoint T B := by
  exact ⟨h.x, h.mem_tripleAdditiveKernelSubmodule, h.nondegenerate, h.small⟩

/-- A small nondegenerate kernel point gives the small Pasten-candidate existence predicate. -/
theorem SmallNondegenerateKernelPoint.hasSmallPastenCandidate
    {T : ABCTriple} {B : ℤ}
    (h : SmallNondegenerateKernelPoint T B) :
    HasSmallPastenCandidate T B := by
  exact ⟨h.x, (mem_tripleAdditiveKernelSubmodule_iff T h.x).1 h.mem_kernel,
    h.nondegenerate, h.small⟩

/--
The small Pasten-candidate existence predicate implies the small kernel-point
existence predicate.
-/
theorem hasSmallNondegenerateKernelPoint_of_hasSmallPastenCandidate
    {T : ABCTriple} {B : ℤ}
    (h : HasSmallPastenCandidate T B) :
    HasSmallNondegenerateKernelPoint T B := by
  rcases h with ⟨x, hadd, hnd, hsmall⟩
  exact ⟨x, (mem_tripleAdditiveKernelSubmodule_iff T x).2 hadd, hnd, hsmall⟩

/--
A small kernel point gives the small Pasten-candidate existence predicate.
-/
theorem hasSmallPastenCandidate_of_hasSmallNondegenerateKernelPoint
    {T : ABCTriple} {B : ℤ}
    (h : HasSmallNondegenerateKernelPoint T B) :
    HasSmallPastenCandidate T B := by
  rcases h with ⟨x, hmem, hnd, hsmall⟩
  exact ⟨x, (mem_tripleAdditiveKernelSubmodule_iff T x).1 hmem, hnd, hsmall⟩

/--
Small Pasten candidates are exactly small nondegenerate points in the triple
additive-kernel submodule.
-/
theorem hasSmallPastenCandidate_iff_hasSmallNondegenerateKernelPoint
    (T : ABCTriple) (B : ℤ) :
    HasSmallPastenCandidate T B ↔ HasSmallNondegenerateKernelPoint T B := by
  constructor
  · exact hasSmallNondegenerateKernelPoint_of_hasSmallPastenCandidate
  · exact hasSmallPastenCandidate_of_hasSmallNondegenerateKernelPoint

/-- Forget the smallness bound from a small Pasten-candidate existence predicate. -/
theorem hasPastenCandidate_of_hasSmallPastenCandidate
    {T : ABCTriple} {B : ℤ}
    (h : HasSmallPastenCandidate T B) : HasPastenCandidate T := by
  rcases h with ⟨x, hadd, hnd, _hsmall⟩
  exact ⟨x, hadd, hnd⟩

/-- Forget the smallness bound from a small kernel-point existence predicate. -/
theorem hasPastenCandidate_of_hasSmallNondegenerateKernelPoint
    {T : ABCTriple} {B : ℤ}
    (h : HasSmallNondegenerateKernelPoint T B) : HasPastenCandidate T := by
  exact hasPastenCandidate_of_hasSmallPastenCandidate
    (hasSmallPastenCandidate_of_hasSmallNondegenerateKernelPoint h)

@[simp] theorem SmallPastenCandidate.toSmallNondegenerateKernelPoint_x
    {T : ABCTriple} {B : ℤ} (h : SmallPastenCandidate T B) :
    h.toSmallNondegenerateKernelPoint.x = h.x := rfl

@[simp] theorem SmallNondegenerateKernelPoint.toSmallPastenCandidate_x
    {T : ABCTriple} {B : ℤ} (h : SmallNondegenerateKernelPoint T B) :
    h.toSmallPastenCandidate.x = h.x := rfl

@[simp] theorem SmallPastenStyleDerivative.toSmallNondegenerateKernelPoint_x
    {T : ABCTriple} {B : ℤ} (h : SmallPastenStyleDerivative T B) :
    h.toSmallNondegenerateKernelPoint.x = h.x := rfl

end ABD
