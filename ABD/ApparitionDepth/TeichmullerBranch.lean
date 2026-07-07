/-
  ABD.ApparitionDepth.TeichmullerBranch

  Step 13 of the Apparition-Depth Decomposition project.

  This file introduces the finite-level language for the generated representative

      omega_{p,d,j}[r]

  on the residue-ring side.  It is deliberately finite-level and lightweight:
  the actual p-adic / Witt-vector Teichmuller construction is postponed to a
  later file.

  The intended mathematical picture is:

    * `p` is the target prime;
    * `d` is a divisor of `p - 1`;
    * `j` is a branch index with `1 <= j <= d` and `gcd j d = 1`;
    * `omega` is a representative modulo `p^r` whose `d`-th power is one;
    * a base `ell` in the same residue class as `omega` modulo `p^r` inherits
      the Core depth statement `p^r | ell^d - 1` by the bridge proved earlier.

  The important point for now is not uniqueness of the lift, but the interface:
  once a later Hensel/Teichmuller construction produces an `omega`, this file
  already knows how to send it into `MovingBaseClass`, and hence into Core depth.
-/

import ABD.ApparitionDepth.DepthValueBridgeProof

namespace ApparitionDepth

/-! ## Branch parameters -/

/-- The branch index condition for `j` at order `d`.

This records the user-facing convention:

`1 <= j <= d` and `gcd(j,d)=1`.

The condition `0 < d` is included so that the interval is meaningful. -/
def BranchIndex (d j : Nat) : Prop :=
  0 < d ∧ 1 ≤ j ∧ j ≤ d ∧ j.Coprime d

/-- The finite branch parameter package for `omega_{p,d,j}`.

Mathematically, `d | p - 1` says that a `d`-th root branch can live in the
multiplicative group modulo `p`.  Prime assumptions on `p` are intentionally not
baked into this lightweight predicate; later theorem layers can add them when
needed. -/
def BranchParams (p d j : Nat) : Prop :=
  0 < p ∧ d ∣ p - 1 ∧ BranchIndex d j

/-- A generator-based seed condition modulo `p`.

If `g` is later assumed to be a primitive root modulo `p`, then

`g ^ (((p - 1) / d) * j)`

is the usual branch seed modulo `p`.  This file only records the residue formula;
primitive-root hypotheses are postponed to the Hensel/Teichmuller construction
layer. -/
def BranchSeedModP (g omega p d j : Nat) : Prop :=
  (omega : ZMod p) = ((g : ZMod p) ^ (((p - 1) / d) * j))

/-! ## Finite-level omega representatives -/

/-- `omega` is a `d`-th-root representative at precision `p^r`. -/
def OmegaRootAtLevel (omega p d r : Nat) : Prop :=
  ResidueDepthAtLeast omega p d r

/-- A finite-level branch representative with an explicit seed generator `g`.

This is the first Lean-facing form of

`omega_{p,d,j}[r]`.

It says:

* the branch parameters are admissible;
* `omega` has the expected seed modulo `p`;
* `omega^d = 1` modulo `p^r`. -/
def OmegaBranchAtLevel (g omega p d j r : Nat) : Prop :=
  BranchParams p d j ∧ BranchSeedModP g omega p d j ∧ OmegaRootAtLevel omega p d r

/-- Existence-style finite-level representative for the branch `j`.

The generator `g` is hidden existentially.  Later files can replace this by a
more structured primitive-root or Teichmuller object. -/
def OmegaRepresentative (omega p d j r : Nat) : Prop :=
  ∃ g : Nat, OmegaBranchAtLevel g omega p d j r

/-- A base `ell` lies in the finite-level omega branch represented by `omega` if
`ell` and `omega` are the same modulo `p^r`, and `omega` is a branch
representative. -/
def BaseInOmegaBranch (ell omega p d j r : Nat) : Prop :=
  (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) ∧
    OmegaRepresentative omega p d j r

/-! ## Basic projections -/

theorem branchIndex_pos {d j : Nat}
    (h : BranchIndex d j) :
    0 < d :=
  h.1

theorem branchIndex_one_le {d j : Nat}
    (h : BranchIndex d j) :
    1 ≤ j :=
  h.2.1

theorem branchIndex_le {d j : Nat}
    (h : BranchIndex d j) :
    j ≤ d :=
  h.2.2.1

theorem branchIndex_coprime {d j : Nat}
    (h : BranchIndex d j) :
    j.Coprime d :=
  h.2.2.2

theorem branchParams_p_pos {p d j : Nat}
    (h : BranchParams p d j) :
    0 < p :=
  h.1

theorem branchParams_dvd {p d j : Nat}
    (h : BranchParams p d j) :
    d ∣ p - 1 :=
  h.2.1

theorem branchParams_index {p d j : Nat}
    (h : BranchParams p d j) :
    BranchIndex d j :=
  h.2.2

theorem omegaBranchAtLevel_params {g omega p d j r : Nat}
    (h : OmegaBranchAtLevel g omega p d j r) :
    BranchParams p d j :=
  h.1

theorem omegaBranchAtLevel_seed {g omega p d j r : Nat}
    (h : OmegaBranchAtLevel g omega p d j r) :
    BranchSeedModP g omega p d j :=
  h.2.1

theorem omegaBranchAtLevel_root {g omega p d j r : Nat}
    (h : OmegaBranchAtLevel g omega p d j r) :
    OmegaRootAtLevel omega p d r :=
  h.2.2

theorem omegaRepresentative_root {omega p d j r : Nat}
    (h : OmegaRepresentative omega p d j r) :
    ResidueDepthAtLeast omega p d r := by
  rcases h with ⟨g, hg⟩
  exact omegaBranchAtLevel_root hg

theorem baseInOmegaBranch_congr {ell omega p d j r : Nat}
    (h : BaseInOmegaBranch ell omega p d j r) :
    (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)) :=
  h.1

theorem baseInOmegaBranch_omega {ell omega p d j r : Nat}
    (h : BaseInOmegaBranch ell omega p d j r) :
    OmegaRepresentative omega p d j r :=
  h.2

/-! ## Connection to the existing moving-base/Core bridge -/

/-- An omega branch membership is a `MovingBaseClass`. -/
theorem movingBaseClass_of_baseInOmegaBranch {ell omega p d j r : Nat}
    (h : BaseInOmegaBranch ell omega p d j r) :
    MovingBaseClass ell omega p d r :=
  ⟨baseInOmegaBranch_congr h, omegaRepresentative_root (baseInOmegaBranch_omega h)⟩

/-- Therefore a positive base in an omega branch has Core depth at least `r`. -/
theorem depthAtLeast_of_baseInOmegaBranch_of_base_pos
    {ell omega p d j r : Nat}
    (h : BaseInOmegaBranch ell omega p d j r)
    (hell_pos : 0 < ell) :
    DepthAtLeast ell p d r :=
  depthAtLeast_of_movingBaseClass_of_base_pos
    (movingBaseClass_of_baseInOmegaBranch h) hell_pos

/-- With the standard valuation assumptions, membership in an omega branch gives
`r <= depthValue ell p d`. -/
theorem le_depthValue_of_baseInOmegaBranch
    {ell omega p d j r : Nat}
    [Fact (Nat.Prime p)]
    (hN : N ell d ≠ 0)
    (h : BaseInOmegaBranch ell omega p d j r)
    (hell_pos : 0 < ell) :
    r ≤ depthValue ell p d :=
  le_depthValue_of_depthAtLeast hN
    (depthAtLeast_of_baseInOmegaBranch_of_base_pos h hell_pos)

end ApparitionDepth
