/-
Copyright (c) 2026 NOIZ. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NOIZ
-/
import ABD.Lattice.KernelSubmodule
import ABD.Lattice.PastenStyle

namespace ABD

/--
A `PastenCandidate` is, in particular, a point of the additive-kernel
submodule attached to its triple.

This is the first bridge from the Pasten-style packaging back to the
linear-algebra object used by the lattice layer.
-/
theorem PastenCandidate.mem_tripleAdditiveKernelSubmodule
    {T : ABCTriple} (h : PastenCandidate T) :
    h.x ∈ TripleAdditiveKernelSubmodule T := by
  exact (mem_tripleAdditiveKernelSubmodule_iff T h.x).2 h.additive

/-- A bounded Pasten candidate also lies in the triple additive-kernel submodule. -/
theorem SmallPastenCandidate.mem_tripleAdditiveKernelSubmodule
    {T : ABCTriple} {B : ℤ} (h : SmallPastenCandidate T B) :
    h.x ∈ TripleAdditiveKernelSubmodule T := by
  exact (mem_tripleAdditiveKernelSubmodule_iff T h.x).2 h.additive

/--
A fully packaged Pasten-style derivative is still a point of the additive-kernel
submodule.  The stored Leibniz fields are irrelevant for this membership; the
additive field is exactly the kernel equation.
-/
theorem PastenStyleDerivative.mem_tripleAdditiveKernelSubmodule
    {T : ABCTriple} (h : PastenStyleDerivative T) :
    h.x ∈ TripleAdditiveKernelSubmodule T := by
  exact (mem_tripleAdditiveKernelSubmodule_iff T h.x).2 h.additive

/-- A small fully packaged Pasten-style derivative lies in the kernel submodule. -/
theorem SmallPastenStyleDerivative.mem_tripleAdditiveKernelSubmodule
    {T : ABCTriple} {B : ℤ} (h : SmallPastenStyleDerivative T B) :
    h.x ∈ TripleAdditiveKernelSubmodule T := by
  exact (mem_tripleAdditiveKernelSubmodule_iff T h.x).2 h.additive

end ABD
