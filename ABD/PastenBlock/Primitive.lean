import ABD.PastenBlock.Hyperplane

namespace ABD

/-- An arithmetic primitive triple in the pairwise-coprime form needed by the
support-block decomposition.

For an additive triple `a + b = c`, this is the usual primitive situation:
there is no prime direction shared by two of `a`, `b`, and `c`.  The file keeps
this pairwise form separate from the support-level predicate
`SupportBlocksDisjoint`, so the arithmetic and block-normal-form layers remain
cleanly separated. -/
structure ABCTriple.Primitive (T : ABCTriple) : Prop where
  coprimeAB : Nat.Coprime T.a T.b
  coprimeAC : Nat.Coprime T.a T.c
  coprimeBC : Nat.Coprime T.b T.c

/-- Membership in `supp n` means the corresponding factorization coefficient is
nonzero. -/
theorem factorization_ne_zero_of_mem_supp {n p : ℕ} (hp : p ∈ supp n) :
    n.factorization p ≠ 0 := by
  have hp_support : p ∈ n.factorization.support := by
    rw [Nat.support_factorization]
    simpa [supp] using hp
  exact Finsupp.mem_support_iff.mp hp_support

/-- A support prime direction actually divides the integer. -/
theorem dvd_of_mem_supp {n p : ℕ} (hp : p ∈ supp n) : p ∣ n := by
  by_contra hnot
  exact (factorization_ne_zero_of_mem_supp hp)
    (Nat.factorization_eq_zero_of_not_dvd hnot)

/-- The prime-support layer never contains the direction `1`. -/
theorem ne_one_of_mem_supp {n p : ℕ} (hp : p ∈ supp n) : p ≠ 1 := by
  intro hp_one
  exact (factorization_ne_zero_of_mem_supp hp) (by
    simp [hp_one, Nat.factorization_one_right n])

/-- If two integers are coprime, their prime-support layers do not intersect. -/
theorem not_mem_supp_right_of_coprime
    {m n p : ℕ} (hcop : Nat.Coprime m n) (hm : p ∈ supp m) :
    p ∉ supp n := by
  intro hn
  have hpm : p ∣ m := dvd_of_mem_supp hm
  have hpn : p ∣ n := dvd_of_mem_supp hn
  have hpgcd : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm hpn
  have hgcd : Nat.gcd m n = 1 := hcop
  have hp_dvd_one : p ∣ 1 := by
    rw [← hgcd]
    exact hpgcd
  have hp_one : p = 1 := Nat.dvd_one.mp hp_dvd_one
  exact (ne_one_of_mem_supp hm) hp_one

/-- Symmetric form of support disjointness for coprime integers. -/
theorem not_mem_supp_left_of_coprime
    {m n p : ℕ} (hcop : Nat.Coprime m n) (hn : p ∈ supp n) :
    p ∉ supp m := by
  intro hm
  exact not_mem_supp_right_of_coprime hcop hm hn

/-- Pairwise arithmetic primitivity implies the support-level primitive predicate
used by the block direct-sum normal form. -/
theorem ABCTriple.supportBlocksDisjoint_of_primitive
    (T : ABCTriple) (hprim : T.Primitive) : T.SupportBlocksDisjoint where
  disjointAB := by
    intro p hpA hpB
    exact not_mem_supp_right_of_coprime hprim.coprimeAB
      (by simpa [ABCTriple.supportA] using hpA)
      (by simpa [ABCTriple.supportB] using hpB)
  disjointAC := by
    intro p hpA hpC
    exact not_mem_supp_right_of_coprime hprim.coprimeAC
      (by simpa [ABCTriple.supportA] using hpA)
      (by simpa [ABCTriple.supportC] using hpC)
  disjointBC := by
    intro p hpB hpC
    exact not_mem_supp_right_of_coprime hprim.coprimeBC
      (by simpa [ABCTriple.supportB] using hpB)
      (by simpa [ABCTriple.supportC] using hpC)

/-- Pairwise arithmetic primitivity implies `PrimitiveSupport`. -/
theorem ABCTriple.primitiveSupport_of_primitive
    (T : ABCTriple) (hprim : T.Primitive) : T.PrimitiveSupport :=
  T.supportBlocksDisjoint_of_primitive hprim

/-- Under arithmetic primitivity, glued blocks satisfy Pasten's additive condition
exactly when they satisfy block balance. -/
theorem ABCTriple.glueBlocks_mem_pastenT_iff_blockBalance_of_primitive
    (T : ABCTriple) (hprim : T.Primitive) (x : T.TangentBlocks) :
    T.glueBlocks x ∈ PastenT T ↔ T.BlockBalance x := by
  exact T.glueBlocks_mem_pastenT_iff_blockBalance
    (T.supportBlocksDisjoint_of_primitive hprim) x

/-- Under arithmetic primitivity, a glued block candidate is strict Pasten data
exactly when it satisfies block balance and avoids the `a/b` Wronskian
hyperplane. -/
theorem ABCTriple.strictCandidate_iff_blockBalance_and_ab_hyperplane_avoidance_of_primitive
    (T : ABCTriple) (hprim : T.Primitive) (x : T.TangentBlocks) :
    (T.glueBlocks x ∈ PastenT T ∧ T.PastenNondegenerate (T.glueBlocks x)) ↔
      T.BlockBalance x ∧ (x.xA, x.xB) ∉ T.ABWronskianHyperplane := by
  exact T.strictCandidate_iff_blockBalance_and_ab_hyperplane_avoidance
    (T.supportBlocksDisjoint_of_primitive hprim) x

end ABD
