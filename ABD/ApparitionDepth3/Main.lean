/-
  ABD.ApparitionDepth3.Main

  Main public surface for the independent organic rebuild.
-/

import ABD.ApparitionDepth3.GeneratedRoot

namespace ApparitionDepth3

/-- Main generated root-at-level theorem. -/
theorem main_generated_rootAtLevel {ell seed p d r : Nat}
    (hgen : GeneratedRoot ell seed p d r) :
    RootAtLevel ell p d r :=
  generated_rootAtLevel hgen

/-- Main generated depth theorem. -/
theorem main_generated_depthAtLeast {ell seed p d r : Nat}
    (hgen : GeneratedRoot ell seed p d r)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  generated_depthAtLeast hgen hell_pos

/-- Main finite-Hensel existence theorem. -/
theorem main_exists_generatedRoot_of_kernel {seed p d r : Nat}
    (hkernel : FiniteHenselKernel seed p d)
    (hr_pos : 0 < r) :
    ∃ ell : Nat, GeneratedRoot ell seed p d r :=
  exists_generatedRoot_of_kernel hkernel hr_pos


/-- Main simple-root finite-Hensel theorem. -/
theorem main_exists_generatedRoot_of_simpleRoot {seed p d r : Nat}
    (hsimple : SimpleRootModP seed p d)
    (hlocal : HenselLocalData seed p d)
    (hr_pos : 0 < r) :
    ∃ ell : Nat, GeneratedRoot ell seed p d r :=
  exists_generatedRoot_of_simpleRoot hsimple hlocal hr_pos

/-- Main simple-root root-at-level theorem. -/
theorem main_exists_rootAtLevel_of_simpleRoot {seed p d r : Nat}
    (hsimple : SimpleRootModP seed p d)
    (hlocal : HenselLocalData seed p d)
    (hr_pos : 0 < r) :
    ∃ ell : Nat, RootAtLevel ell p d r :=
  exists_rootAtLevel_of_simpleRoot hsimple hlocal hr_pos

/-- Main current theorem: generated branch plus order control gives first
apparition with depth at least `r`. -/
theorem main_generated_firstAppearsWithDepthAtLeast
    {ell seed p d r : Nat} {hcop : ell.Coprime p}
    (hord : OrderModIs ell p d hcop)
    (hd_pos : 0 < d)
    (hgen : GeneratedRoot ell seed p d r)
    (hell_pos : 0 < ell) :
    FirstAppearsWithDepthAtLeast ell p d r :=
  generated_firstAppearsWithDepthAtLeast hord hd_pos hgen hell_pos

/-!
Future AD3 attachments should target these public shapes:

* Cyclotomic:
  `RootAtLevel ell p d r` + exact order -> depth on `Phi_d(ell)`.

* Primitive divisor:
  primitive prime divisor of `ell^n - 1` -> `FirstAppearsAt ell p n`.

* Witt/carry:
  carry condition at level `r` -> `RootAtLevel ell p d (r+1)`.

The point of AD3 is that all three will attach to `RootAtLevel`, not to the old
chain of residue/omega/interface/final conversions.
-/

end ApparitionDepth3
