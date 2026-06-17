import ABD.PastenBlock.Derivative

namespace ABD

/-- If a prime-direction coefficient is outside the support of `n`, then that
coefficient contributes zero to the formal derivative of `n`.

This is the local coefficient fact behind the block restriction theorems below:
coordinates outside `supp n` may be present in a larger ambient support, but
`v_p(n)` vanishes there. -/
theorem derivCoeff_eq_zero_of_not_mem_supp {n p : ℕ}
    (hp : p ∉ supp n) : derivCoeff n p = 0 := by
  have hp' : p ∉ n.factorization.support := by
    simpa only [supp] using hp
  have hval : val n p = 0 := by
    unfold val
    exact Finsupp.notMem_support_iff.mp hp'
  unfold derivCoeff
  rw [hval]
  simp

/-- If all terms outside a predicate are zero, the sum over `s` is the same
as the sum over `s.filter P`. -/
private lemma sum_eq_sum_filter_of_zero_not
    {α β : Type*} [AddCommMonoid β]
    (s : Finset α) (P : α → Prop) [DecidablePred P]
    (f : α → β)
    (hzero : ∀ a ∈ s, ¬ P a → f a = 0) :
    Finset.sum s f = Finset.sum (s.filter P) f := by
  have hnot :
      Finset.sum (s.filter (fun a => ¬ P a)) f = 0 := by
    refine Finset.sum_eq_zero ?_
    intro a ha
    rcases Finset.mem_filter.mp ha with ⟨has, hnotP⟩
    exact hzero a has hnotP
  have hsplit :
      Finset.sum (s.filter P) f +
          Finset.sum (s.filter (fun a => ¬ P a)) f =
        Finset.sum s f := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := s) (p := P) (f := f))
  calc
    Finset.sum s f
        = Finset.sum (s.filter P) f +
            Finset.sum (s.filter (fun a => ¬ P a)) f := by
              exact hsplit.symm
    _ = Finset.sum (s.filter P) f := by
              rw [hnot, add_zero]

/-- Inclusion of support coordinates induced by `S ⊆ T`. -/
private def supportSubtypeEmb {S T : Finset ℕ} (hST : S ⊆ T) :
    {p : ℕ // p ∈ S} ↪ {p : ℕ // p ∈ T} where
  toFun hp := ⟨hp.1, hST hp.2⟩
  inj' := by
    intro hp hq h
    exact Subtype.ext
      (congrArg (fun z : {p : ℕ // p ∈ T} => z.1) h)

private lemma sum_filter_supportSubtypeEmb
    {S T : Finset ℕ} (hST : S ⊆ T)
    (f : {p : ℕ // p ∈ T} → ℤ) :
    Finset.sum
        ((Finset.univ : Finset {p : ℕ // p ∈ T}).filter
          (fun hp => hp.1 ∈ S))
        f
      =
    Finset.sum
      (Finset.univ : Finset {p : ℕ // p ∈ S})
      (fun hp => f ((supportSubtypeEmb hST) hp)) := by
  classical
  let e := supportSubtypeEmb hST
  have hmap :
      (Finset.univ : Finset {p : ℕ // p ∈ S}).map e =
        ((Finset.univ : Finset {p : ℕ // p ∈ T}).filter
          (fun hp => hp.1 ∈ S)) := by
    ext hp
    constructor
    · intro h
      rcases Finset.mem_map.mp h with ⟨hpS, _hmem, hEq⟩
      rw [← hEq]
      simp [e, supportSubtypeEmb]
    · intro h
      have hs : hp.1 ∈ S := (Finset.mem_filter.mp h).2
      refine Finset.mem_map.mpr ?_
      refine ⟨⟨hp.1, hs⟩, by simp, ?_⟩
      apply Subtype.ext
      rfl
  calc
    Finset.sum
        ((Finset.univ : Finset {p : ℕ // p ∈ T}).filter
          (fun hp => hp.1 ∈ S))
        f
        =
      Finset.sum
        ((Finset.univ : Finset {p : ℕ // p ∈ S}).map e)
        f := by
          rw [hmap]
    _ =
      Finset.sum
        (Finset.univ : Finset {p : ℕ // p ∈ S})
        (fun hp => f (e hp)) := by
          rw [Finset.sum_map]

/-- Restricting the ambient support to a smaller support containing all
nonzero derivative coefficients does not change the formal derivative.

The hypothesis `hzero` is deliberately coefficient-level: it says exactly that
all coordinates in the larger support but outside the smaller one contribute
zero.  This keeps the lemma usable for the `a`, `b`, and `c` blocks without
baking triple-specific facts into the proof. -/
theorem formalDeriv_restrict_of_coeff_zero
    {S T : Finset ℕ} (hST : S ⊆ T)
    (x : Tangent T) (n : ℕ)
    (hzero : ∀ hp : {p : ℕ // p ∈ T}, hp.1 ∉ S → derivCoeff n hp.1 = 0) :
    formalDeriv T x n =
      formalDeriv S (fun hp => x ⟨hp.1, hST hp.2⟩) n := by
  classical
  unfold formalDeriv
  let f : {p : ℕ // p ∈ T} → ℤ :=
    fun hp => derivCoeff n hp.1 * x hp
  have hfull :
      Finset.sum
          (Finset.univ : Finset {p : ℕ // p ∈ T})
          f
        =
      Finset.sum
          ((Finset.univ : Finset {p : ℕ // p ∈ T}).filter
            (fun hp => hp.1 ∈ S))
          f := by
    apply sum_eq_sum_filter_of_zero_not
    intro hp _hhp hnot
    dsimp [f]
    rw [hzero hp hnot]
    simp
  have hfilter :
      Finset.sum
          ((Finset.univ : Finset {p : ℕ // p ∈ T}).filter
            (fun hp => hp.1 ∈ S))
          f
        =
      Finset.sum
          (Finset.univ : Finset {p : ℕ // p ∈ S})
          (fun hp => f ((supportSubtypeEmb hST) hp)) :=
    sum_filter_supportSubtypeEmb hST f
  calc
    Finset.sum
        (Finset.univ : Finset {p : ℕ // p ∈ T})
        (fun hp => derivCoeff n hp.1 * x hp)
        =
      Finset.sum
        (Finset.univ : Finset {p : ℕ // p ∈ T})
        f := by
          rfl
    _ =
      Finset.sum
        ((Finset.univ : Finset {p : ℕ // p ∈ T}).filter
          (fun hp => hp.1 ∈ S))
        f := hfull
    _ =
      Finset.sum
        (Finset.univ : Finset {p : ℕ // p ∈ S})
        (fun hp => f ((supportSubtypeEmb hST) hp)) := hfilter
    _ =
      Finset.sum
        (Finset.univ : Finset {p : ℕ // p ∈ S})
        (fun hp =>
          derivCoeff n hp.1 * x ⟨hp.1, hST hp.2⟩) := by
          rfl

/-- The full-support derivative of `a` only depends on the `S_a = supp(a)` block. -/
theorem ABCTriple.derivA_eq_formalDeriv_restrictA
    (T : ABCTriple) (x : Tangent T.support) :
    T.derivA x = formalDeriv T.supportA (T.restrictA x) T.a := by
  unfold ABCTriple.derivA ABCTriple.restrictA
  change
    formalDeriv T.support x T.a =
      formalDeriv T.supportA
        (fun hp : {p : ℕ // p ∈ T.supportA} =>
          x ⟨hp.1, T.supportA_subset_support hp.2⟩)
        T.a
  exact
    formalDeriv_restrict_of_coeff_zero
      (S := T.supportA)
      (T := T.support)
      T.supportA_subset_support
      x
      T.a
      (by
        intro hp hnot
        exact derivCoeff_eq_zero_of_not_mem_supp
          (n := T.a)
          (p := hp.1)
          (by
            simpa only [ABCTriple.supportA] using hnot))

/-- The full-support derivative of `b` only depends on the `S_b = supp(b)` block. -/
theorem ABCTriple.derivB_eq_formalDeriv_restrictB
    (T : ABCTriple) (x : Tangent T.support) :
    T.derivB x = formalDeriv T.supportB (T.restrictB x) T.b := by
  unfold ABCTriple.derivB ABCTriple.restrictB
  change
    formalDeriv T.support x T.b =
      formalDeriv T.supportB
        (fun hp : {p : ℕ // p ∈ T.supportB} =>
          x ⟨hp.1, T.supportB_subset_support hp.2⟩)
        T.b
  exact
    formalDeriv_restrict_of_coeff_zero
      (S := T.supportB)
      (T := T.support)
      T.supportB_subset_support
      x
      T.b
      (by
        intro hp hnot
        exact derivCoeff_eq_zero_of_not_mem_supp
          (n := T.b)
          (p := hp.1)
          (by
            simpa only [ABCTriple.supportB] using hnot))

/-- The full-support derivative of `c` only depends on the `S_c = supp(c)` block. -/
theorem ABCTriple.derivC_eq_formalDeriv_restrictC
    (T : ABCTriple) (x : Tangent T.support) :
    T.derivC x = formalDeriv T.supportC (T.restrictC x) T.c := by
  unfold ABCTriple.derivC ABCTriple.restrictC
  change
    formalDeriv T.support x T.c =
      formalDeriv T.supportC
        (fun hp : {p : ℕ // p ∈ T.supportC} =>
          x ⟨hp.1, T.supportC_subset_support hp.2⟩)
        T.c
  exact
    formalDeriv_restrict_of_coeff_zero
      (S := T.supportC)
      (T := T.support)
      T.supportC_subset_support
      x
      T.c
      (by
        intro hp hnot
        exact derivCoeff_eq_zero_of_not_mem_supp
          (n := T.c)
          (p := hp.1)
          (by
            simpa only [ABCTriple.supportC] using hnot))

/-- Pasten's additive equation, now written using only the three restricted
support blocks. -/
theorem ABCTriple.mem_pastenT_iff_restrict_block_equation
    (T : ABCTriple) (x : Tangent T.support) :
    x ∈ PastenT T ↔
      formalDeriv T.supportA (T.restrictA x) T.a +
        formalDeriv T.supportB (T.restrictB x) T.b =
          formalDeriv T.supportC (T.restrictC x) T.c := by
  rw [T.mem_pastenT_iff_block_equation]
  rw [T.derivA_eq_formalDeriv_restrictA]
  rw [T.derivB_eq_formalDeriv_restrictB]
  rw [T.derivC_eq_formalDeriv_restrictC]

end ABD
