import ABD.ABD.PastenBlock.Theorem3

namespace ABD

/-- The normalized `c`-coefficient gcd as a submodule of integer multiples.

This is the submodule version of `cCoeffGCDMultiples`.  It is used to pull the
`c`-adjustability condition back to the `S_a ⊕ S_b` seed side. -/
def ABCTriple.cCoeffGCDMultiplesSubmodule
    (T : ABCTriple) : Submodule ℤ ℤ where
  carrier := {target | (T.cCoeffGCD : ℤ) ∣ target}
  zero_mem' := by
    exact dvd_zero _
  add_mem' := by
    intro x y hx hy
    exact dvd_add hx hy
  smul_mem' := by
    intro r x hx
    exact dvd_mul_of_dvd_right hx r

@[simp]
theorem ABCTriple.mem_cCoeffGCDMultiplesSubmodule_iff
    (T : ABCTriple) (target : ℤ) :
    target ∈ T.cCoeffGCDMultiplesSubmodule ↔
      (T.cCoeffGCD : ℤ) ∣ target := by
  rfl

/-- Additivity of the `a/b` seed target. -/
theorem ABCTriple.abSeedTarget_add
    (T : ABCTriple) (z w : T.ATangent × T.BTangent) :
    T.abSeedTarget (z.1 + w.1) (z.2 + w.2) =
      T.abSeedTarget z.1 z.2 + T.abSeedTarget w.1 w.2 := by
  unfold ABCTriple.abSeedTarget
  rw [formalDeriv_add_tangent]
  rw [formalDeriv_add_tangent]
  simp [add_assoc, add_left_comm, add_comm]

/-- Homogeneity of the `a/b` seed target. -/
theorem ABCTriple.abSeedTarget_smul
    (T : ABCTriple) (k : ℤ) (z : T.ATangent × T.BTangent) :
    T.abSeedTarget (k • z.1) (k • z.2) =
      k • T.abSeedTarget z.1 z.2 := by
  unfold ABCTriple.abSeedTarget
  rw [formalDeriv_smul_tangent]
  rw [formalDeriv_smul_tangent]
  simp [mul_add]

/-- The `a/b` seed target as a linear map on the seed space. -/
noncomputable def ABCTriple.abSeedTargetLinear
    (T : ABCTriple) : (T.ATangent × T.BTangent) →ₗ[ℤ] ℤ where
  toFun z := T.abSeedTarget z.1 z.2
  map_add' := by
    intro z w
    exact T.abSeedTarget_add z w
  map_smul' := by
    intro k z
    exact T.abSeedTarget_smul k z

@[simp]
theorem ABCTriple.abSeedTargetLinear_apply
    (T : ABCTriple) (z : T.ATangent × T.BTangent) :
    T.abSeedTargetLinear z = T.abSeedTarget z.1 z.2 := by
  rfl

/-- The `a/b` seed submodule whose targets are compatible with the `c`-side gcd.

By Theorem 3, this is exactly the set of `a/b` seeds that can be adjusted on the
`c` side, after forgetting the actual choice of lift. -/
def ABCTriple.ABGCDCompatibleSubmodule
    (T : ABCTriple) : Submodule ℤ (T.ATangent × T.BTangent) where
  carrier := {z | (T.cCoeffGCD : ℤ) ∣ T.abSeedTarget z.1 z.2}
  zero_mem' := by
    change (T.cCoeffGCD : ℤ) ∣
      T.abSeedTarget (0 : T.ATangent) (0 : T.BTangent)
    unfold ABCTriple.abSeedTarget
    simp [formalDeriv]
  add_mem' := by
    intro z w hz hw
    change (T.cCoeffGCD : ℤ) ∣
      T.abSeedTarget (z.1 + w.1) (z.2 + w.2)
    rw [T.abSeedTarget_add z w]
    exact dvd_add hz hw
  smul_mem' := by
    intro k z hz
    change (T.cCoeffGCD : ℤ) ∣
      T.abSeedTarget (k • z.1) (k • z.2)
    rw [T.abSeedTarget_smul]
    exact dvd_mul_of_dvd_right hz k

@[simp]
theorem ABCTriple.mem_ABGCDCompatibleSubmodule_iff
    (T : ABCTriple) (z : T.ATangent × T.BTangent) :
    z ∈ T.ABGCDCompatibleSubmodule ↔
      (T.cCoeffGCD : ℤ) ∣ T.abSeedTarget z.1 z.2 := by
  rfl

/-- There exists an `a/b` seed whose target is compatible with the `c`-side gcd. -/
def ABCTriple.HasGCDCompatibleABSeed (T : ABCTriple) : Prop :=
  ∃ xA : T.ATangent, ∃ xB : T.BTangent,
    (T.cCoeffGCD : ℤ) ∣ T.abSeedTarget xA xB

/-- There exists an `a/b` seed which is both `c`-gcd-compatible and Wronskian
nondegenerate. -/
def ABCTriple.HasNondegenerateGCDCompatibleABSeed (T : ABCTriple) : Prop :=
  ∃ xA : T.ATangent, ∃ xB : T.BTangent,
    (xA, xB) ∉ T.ABWronskianHyperplaneSubmodule ∧
      (T.cCoeffGCD : ℤ) ∣ T.abSeedTarget xA xB

/-- The first precise bad-pattern predicate exposed by Theorems 1--3:
all `c`-gcd-compatible `a/b` seeds fall into the Wronskian-degenerate kernel. -/
def ABCTriple.ABGCDWronskianDegenerate (T : ABCTriple) : Prop :=
  T.ABGCDCompatibleSubmodule ≤ T.ABWronskianHyperplaneSubmodule

/-- The complementary nondegenerate situation: some `c`-gcd-compatible seed avoids
Wronskian degeneration. -/
def ABCTriple.ABGCDWronskianNondegenerate (T : ABCTriple) : Prop :=
  ¬ T.ABGCDWronskianDegenerate

/-- Existence of a nondegenerate gcd-compatible `a/b` seed is exactly failure of
the first bad pattern. -/
theorem ABCTriple.hasNondegenerateGCDCompatibleABSeed_iff_not_ABGCDWronskianDegenerate
    (T : ABCTriple) :
    T.HasNondegenerateGCDCompatibleABSeed ↔
      T.ABGCDWronskianNondegenerate := by
  unfold ABCTriple.HasNondegenerateGCDCompatibleABSeed
  unfold ABCTriple.ABGCDWronskianNondegenerate
  unfold ABCTriple.ABGCDWronskianDegenerate
  constructor
  · intro h hle
    rcases h with ⟨xA, xB, hnot, hdiv⟩
    exact hnot (hle ((T.mem_ABGCDCompatibleSubmodule_iff (xA, xB)).2 hdiv))
  · intro hnotle
    by_contra hno
    apply hnotle
    intro z hz
    by_contra hz_not
    rcases z with ⟨xA, xB⟩
    exact hno ⟨xA, xB, hz_not,
      (T.mem_ABGCDCompatibleSubmodule_iff (xA, xB)).1 hz⟩

end ABD
