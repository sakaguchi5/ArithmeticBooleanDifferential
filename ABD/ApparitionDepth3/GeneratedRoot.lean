/-
  ABD.ApparitionDepth3.GeneratedRoot

  Public generated-root layer.
  This is the AD2 public flow, but now backed by the independent AD3 Hensel
  spine instead of importing the archived folder.
-/

import ABD.ApparitionDepth3.Hensel
import ABD.ApparitionDepth3.Order

namespace ApparitionDepth3

/-- A base is generated at level `r` from a seed if it is the unique lift class
at that level. -/
def GeneratedRoot (ell seed p d r : Nat) : Prop :=
  LiftAtLevel seed ell p d r

/-- A generated root is immediately a root at level `r`. -/
theorem generated_rootAtLevel {ell seed p d r : Nat}
    (hgen : GeneratedRoot ell seed p d r) :
    RootAtLevel ell p d r :=
  hgen.2

/-- A positive generated base has depth at least `r`. -/
theorem generated_depthAtLeast {ell seed p d r : Nat}
    (hgen : GeneratedRoot ell seed p d r)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  depthAtLeast_of_rootAtLevel_of_base_pos hell_pos
    (generated_rootAtLevel hgen)

/-- Finite-Hensel kernel generates some root at every positive level. -/
theorem exists_generatedRoot_of_kernel {seed p d r : Nat}
    (hkernel : FiniteHenselKernel seed p d)
    (hr_pos : 0 < r) :
    ∃ ell : Nat, GeneratedRoot ell seed p d r := by
  rcases existsUniqueLiftAtLevel_of_kernel hkernel hr_pos with
    ⟨ell, hlift, _huniq⟩
  exact ⟨ell, hlift⟩

/-- Finite-Hensel kernel gives an explicit RootAtLevel existence theorem. -/
theorem exists_rootAtLevel_of_kernel {seed p d r : Nat}
    (hkernel : FiniteHenselKernel seed p d)
    (hr_pos : 0 < r) :
    ∃ ell : Nat, RootAtLevel ell p d r := by
  rcases exists_generatedRoot_of_kernel hkernel hr_pos with ⟨ell, hgen⟩
  exact ⟨ell, generated_rootAtLevel hgen⟩

/-- Generated branch plus order control gives first apparition with depth. -/
theorem generated_firstAppearsWithDepthAtLeast
    {ell seed p d r : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hgen : GeneratedRoot ell seed p d r)
    (hell_pos : 0 < ell) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  firstWithDepth_of_order_and_depth hord hd_pos hell_pos
    (generated_depthAtLeast hgen hell_pos)

/-! ## Generated roots directly from simple roots

These are the AD3-facing consequences of the local-data Hensel theorem.  The
external theorem placeholder has been removed: callers now provide the local quotient,
correction, expansion, and uniqueness data as `HenselLocalData` until those data
are proved in concrete lower files.
-/

/-- A simple root plus local Hensel data generates a compatible root at every
positive level. -/
theorem exists_generatedRoot_of_simpleRoot
    {seed p d r : Nat}
    (hsimple : SimpleRootModP seed p d)
    (hlocal : HenselLocalData seed p d)
    (hr_pos : 0 < r) :
    ∃ ell : Nat, GeneratedRoot ell seed p d r := by
  rcases existsUniqueLiftAtLevel_of_simpleRoot hsimple hlocal hr_pos with
    ⟨ell, hlift, _huniq⟩
  exact ⟨ell, hlift⟩

/-- A simple root plus local Hensel data generates an explicit RootAtLevel
existence theorem. -/
theorem exists_rootAtLevel_of_simpleRoot
    {seed p d r : Nat}
    (hsimple : SimpleRootModP seed p d)
    (hlocal : HenselLocalData seed p d)
    (hr_pos : 0 < r) :
    ∃ ell : Nat, RootAtLevel ell p d r := by
  rcases exists_generatedRoot_of_simpleRoot hsimple hlocal hr_pos with ⟨ell, hgen⟩
  exact ⟨ell, generated_rootAtLevel hgen⟩

end ApparitionDepth3
