/-
Copyright (c) 2026 NOIZ. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NOIZ
-/
import ABD.Lattice.KernelSubmodule
import ABD.Lattice.Smallness
import ABD.Lattice.Wronskian

namespace ABD

/--
Pasten's `T(a,b)` in the current ABD coordinates, specialized to an `ABCTriple`.

This is intentionally not a new tangent space.  It is the same additive-kernel
condition already used by the lattice layer, now given a Pasten-facing name:

`x ∈ PastenT T` means that the formal derivative reconstructed from the prime
coordinates of `x` satisfies `D_x(a) + D_x(b) = D_x(c)` on the triple.

The support is exactly `T.support = supp(a) ∪ supp(b) ∪ supp(c)`, so directions
outside the Pasten support are absent rather than silently added.
-/
def PastenT (T : ABCTriple) : Set (Tangent T.support) :=
  {x | AdditiveOn T.support x T.a T.b T.c}

@[simp]
theorem mem_pastenT_iff (T : ABCTriple) (x : Tangent T.support) :
    x ∈ PastenT T ↔ AdditiveOn T.support x T.a T.b T.c := by
  rfl

/-- `PastenT` is exactly the existing triple additive kernel, only renamed with
Pasten's notation in mind. -/
@[simp]
theorem pastenT_eq_tripleAdditiveKernel (T : ABCTriple) :
    PastenT T = TripleAdditiveKernel T := by
  rfl

/-- Membership in `PastenT` is equivalent to membership in the submodule version
of the same additive kernel. -/
theorem mem_pastenT_iff_mem_tripleAdditiveKernelSubmodule
    (T : ABCTriple) (x : Tangent T.support) :
    x ∈ PastenT T ↔ x ∈ TripleAdditiveKernelSubmodule T := by
  rw [mem_pastenT_iff, mem_tripleAdditiveKernelSubmodule_iff]

/--
A Pasten-respecting candidate: an element of `T(a,b)` with the actual Wronskian
nondegeneracy condition.

This is stricter than the older pre-Siegel `PastenCandidate`, whose
`Nondegenerate` field is currently only coordinatewise nonzeroness.  Use this
structure for statements meant to track Pasten's original `T(a,b)` plus
`W^ψ(a,b) ≠ 0`.
-/
structure StrictPastenCandidate (T : ABCTriple) where
  x : Tangent T.support
  mem_T : x ∈ PastenT T
  nondegenerate : T.PastenNondegenerate x

/-- A small Pasten-respecting candidate.  The smallness predicate is still the
current coordinatewise placeholder; the Wronskian condition is already the
Pasten-facing one. -/
structure SmallStrictPastenCandidate (T : ABCTriple) (B : ℤ) where
  x : Tangent T.support
  mem_T : x ∈ PastenT T
  nondegenerate : T.PastenNondegenerate x
  small : SmallTangent T.support x B

/-- Forget the smallness field. -/
def SmallStrictPastenCandidate.toStrictPastenCandidate
    {T : ABCTriple} {B : ℤ} (h : SmallStrictPastenCandidate T B) :
    StrictPastenCandidate T where
  x := h.x
  mem_T := h.mem_T
  nondegenerate := h.nondegenerate

/-- A strict candidate satisfies the additive condition by definition of `T(a,b)`. -/
theorem StrictPastenCandidate.additive
    {T : ABCTriple} (h : StrictPastenCandidate T) :
    AdditiveOn T.support h.x T.a T.b T.c := by
  exact (mem_pastenT_iff T h.x).1 h.mem_T

/-- A small strict candidate satisfies the additive condition by definition of `T(a,b)`. -/
theorem SmallStrictPastenCandidate.additive
    {T : ABCTriple} {B : ℤ} (h : SmallStrictPastenCandidate T B) :
    AdditiveOn T.support h.x T.a T.b T.c := by
  exact (mem_pastenT_iff T h.x).1 h.mem_T

/-- A strict Pasten candidate is a point of the triple additive-kernel submodule. -/
theorem StrictPastenCandidate.mem_tripleAdditiveKernelSubmodule
    {T : ABCTriple} (h : StrictPastenCandidate T) :
    h.x ∈ TripleAdditiveKernelSubmodule T := by
  exact (mem_pastenT_iff_mem_tripleAdditiveKernelSubmodule T h.x).1 h.mem_T

/-- A small strict Pasten candidate is a point of the triple additive-kernel submodule. -/
theorem SmallStrictPastenCandidate.mem_tripleAdditiveKernelSubmodule
    {T : ABCTriple} {B : ℤ} (h : SmallStrictPastenCandidate T B) :
    h.x ∈ TripleAdditiveKernelSubmodule T := by
  exact (mem_pastenT_iff_mem_tripleAdditiveKernelSubmodule T h.x).1 h.mem_T

/-- Existence of a strict Pasten candidate. -/
def HasStrictPastenCandidate (T : ABCTriple) : Prop :=
  ∃ x : Tangent T.support,
    x ∈ PastenT T ∧ T.PastenNondegenerate x

/-- Existence of a small strict Pasten candidate. -/
def HasSmallStrictPastenCandidate (T : ABCTriple) (B : ℤ) : Prop :=
  ∃ x : Tangent T.support,
    x ∈ PastenT T ∧ T.PastenNondegenerate x ∧ SmallTangent T.support x B

/-- Bundled strict candidates give the corresponding existence predicate. -/
theorem StrictPastenCandidate.hasStrictPastenCandidate
    {T : ABCTriple} (h : StrictPastenCandidate T) :
    HasStrictPastenCandidate T := by
  exact ⟨h.x, h.mem_T, h.nondegenerate⟩

/-- Bundled small strict candidates give the corresponding existence predicate. -/
theorem SmallStrictPastenCandidate.hasSmallStrictPastenCandidate
    {T : ABCTriple} {B : ℤ} (h : SmallStrictPastenCandidate T B) :
    HasSmallStrictPastenCandidate T B := by
  exact ⟨h.x, h.mem_T, h.nondegenerate, h.small⟩

/-- Forget the size bound from a small strict candidate existence statement. -/
theorem hasStrictPastenCandidate_of_hasSmallStrictPastenCandidate
    {T : ABCTriple} {B : ℤ}
    (h : HasSmallStrictPastenCandidate T B) :
    HasStrictPastenCandidate T := by
  rcases h with ⟨x, hT, hnd, _hsmall⟩
  exact ⟨x, hT, hnd⟩

@[simp]
theorem SmallStrictPastenCandidate.toStrictPastenCandidate_x
    {T : ABCTriple} {B : ℤ} (h : SmallStrictPastenCandidate T B) :
    h.toStrictPastenCandidate.x = h.x := rfl

end ABD
