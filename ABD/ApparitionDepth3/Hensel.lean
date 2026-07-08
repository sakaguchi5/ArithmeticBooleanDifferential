/-
  ABD.ApparitionDepth3.Hensel

  Finite induction layer.

  The local algebra is supplied by `FiniteHenselKernel`; this file proves once
  and for all that such a kernel gives a unique compatible lift at every positive
  precision.  Consequences from a simple root now also take explicit
  `HenselLocalData`, so no external theorem placeholder is used.
-/

import ABD.ApparitionDepth3.HenselStep

namespace ApparitionDepth3

/-- Finite Hensel induction: the kernel produces a unique lift at every positive
precision. -/
theorem existsUniqueLiftAtLevel_of_kernel {seed p d r : Nat}
    (hkernel : FiniteHenselKernel seed p d)
    (hr_pos : 0 < r) :
    ExistsUniqueLiftAtLevel seed p d r := by
  revert hr_pos
  induction r with
  | zero =>
      intro hr_pos
      exact False.elim ((Nat.not_lt_zero 0) hr_pos)
  | succ n ih =>
      intro _hpos
      cases n with
      | zero =>
          simpa using existsUniqueLiftAtLevel_one_of_kernel hkernel
      | succ k =>
          have hk_pos : 0 < k + 1 := Nat.succ_pos k
          have hprev : ExistsUniqueLiftAtLevel seed p d (k + 1) := ih hk_pos
          rcases hprev with ⟨omega, homega, huniqOld⟩
          rcases hkernel.step_exists (k + 1) hk_pos omega homega with
            ⟨omegaNext, hnext, hreduce⟩
          refine ⟨omegaNext, hnext, ?_⟩
          intro omegaNext' hnext'
          have hdown : LiftAtLevel seed omegaNext' p d (k + 1) :=
            liftAtLevel_descend hkernel hk_pos hnext'
          have hreduce' :
              (omegaNext' : ZMod (p ^ (k + 1))) =
                (omega : ZMod (p ^ (k + 1))) :=
            huniqOld omegaNext' hdown
          exact hkernel.step_unique (k + 1) hk_pos omega omegaNext' omegaNext
            homega hnext' hreduce' hnext hreduce

/-- Extract a root at level from the finite-Hensel theorem. -/
theorem rootAtLevel_of_kernel {seed p d r : Nat}
    (hkernel : FiniteHenselKernel seed p d)
    (hr_pos : 0 < r) :
    ∃ omega : Nat, RootAtLevel omega p d r := by
  rcases existsUniqueLiftAtLevel_of_kernel hkernel hr_pos with
    ⟨omega, hlift, _huniq⟩
  exact ⟨omega, hlift.2⟩

/-- A simple root, together with the local Hensel algebra, has a unique
compatible finite lift at every positive level. -/
theorem existsUniqueLiftAtLevel_of_simpleRoot
    {seed p d r : Nat}
    (hsimple : SimpleRootModP seed p d)
    (hlocal : HenselLocalData seed p d)
    (hr_pos : 0 < r) :
    ExistsUniqueLiftAtLevel seed p d r :=
  existsUniqueLiftAtLevel_of_kernel
    (finiteHenselKernel_of_simpleRoot hsimple hlocal) hr_pos

/-- Seed-simple-root spelling. -/
theorem existsUniqueLiftAtLevel_of_seedSimpleRoot
    {seed p d r : Nat}
    (hsimple : SeedSimpleRootModP seed p d)
    (hlocal : HenselLocalData seed p d)
    (hr_pos : 0 < r) :
    ExistsUniqueLiftAtLevel seed p d r :=
  existsUniqueLiftAtLevel_of_simpleRoot hsimple hlocal hr_pos

/-- A simple root, together with the local Hensel algebra, produces a root at
every positive level. -/
theorem rootAtLevel_of_simpleRoot
    {seed p d r : Nat}
    (hsimple : SimpleRootModP seed p d)
    (hlocal : HenselLocalData seed p d)
    (hr_pos : 0 < r) :
    ∃ omega : Nat, RootAtLevel omega p d r :=
  rootAtLevel_of_kernel
    (finiteHenselKernel_of_simpleRoot hsimple hlocal) hr_pos

end ApparitionDepth3
