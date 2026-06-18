import Mathlib.Data.Nat.Factorization.Basic
import ABD.ABD.Examples.ConcreteKernel235
import ABD.ABD.Examples.PastenTwoThreeFive
import ABD.ABD.Lattice.PastenStyle

namespace ABD.Examples

/-- The concrete nonzero kernel tangent from `S235`, now viewed directly on
`twoThreeFiveTriple.support`.

This is the first fully bundled concrete Pasten-style example on the canonical
support attached to the ABC triple `2 + 3 = 5`, rather than on the hand-written
support `{2, 3, 5}`.
-/
def kernelTangent235OnTriple : ABD.Tangent twoThreeFiveTriple.support :=
  fun hp => kernelTangent235_nat hp.1

private lemma factorization_prime_self' {p : ℕ} (hp : Nat.Prime p) :
    (Nat.factorization p) p = 1 :=
  Nat.Prime.factorization_self hp

private lemma factorization_prime_other' {n p : ℕ} (h : ¬ p ∣ n) :
    (Nat.factorization n) p = 0 :=
  Nat.factorization_eq_zero_of_not_dvd h

@[simp] private lemma factorization_2_2' : (Nat.factorization 2) 2 = 1 :=
  factorization_prime_self' (by decide : Nat.Prime 2)

@[simp] private lemma factorization_2_3' : (Nat.factorization 2) 3 = 0 :=
  factorization_prime_other' (by decide : ¬ 3 ∣ 2)

@[simp] private lemma factorization_2_5' : (Nat.factorization 2) 5 = 0 :=
  factorization_prime_other' (by decide : ¬ 5 ∣ 2)

@[simp] private lemma factorization_3_2' : (Nat.factorization 3) 2 = 0 :=
  factorization_prime_other' (by decide : ¬ 2 ∣ 3)

@[simp] private lemma factorization_3_3' : (Nat.factorization 3) 3 = 1 :=
  factorization_prime_self' (by decide : Nat.Prime 3)

@[simp] private lemma factorization_3_5' : (Nat.factorization 3) 5 = 0 :=
  factorization_prime_other' (by decide : ¬ 5 ∣ 3)

@[simp] private lemma factorization_5_2' : (Nat.factorization 5) 2 = 0 :=
  factorization_prime_other' (by decide : ¬ 2 ∣ 5)

@[simp] private lemma factorization_5_3' : (Nat.factorization 5) 3 = 0 :=
  factorization_prime_other' (by decide : ¬ 3 ∣ 5)

@[simp] private lemma factorization_5_5' : (Nat.factorization 5) 5 = 1 :=
  factorization_prime_self' (by decide : Nat.Prime 5)

/-- The canonical support of `2 + 3 = 5` is exactly `{2, 3, 5}`. -/
private lemma mem_twoThreeFiveTriple_support_iff (n : ℕ) :
    n ∈ twoThreeFiveTriple.support ↔ n = 2 ∨ n = 3 ∨ n = 5 := by
  simp only [
    ABCTriple.support,
    supp,
    twoThreeFiveTriple,
    Nat.support_factorization,
    Finset.mem_union,
    Nat.mem_primeFactors,
    ne_eq,
    OfNat.ofNat_ne_zero,
    not_false_eq_true,
    and_true
  ]
  apply Iff.intro
  · -- 左から右への証明
    intro h
    rcases h with ⟨hp, hd⟩ | ⟨hp, hd⟩ | ⟨hp, hd⟩
    · -- case: n | 2
      have h1_or_2 : n = 1 ∨ n = 2 :=
        (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd
      rcases h1_or_2 with rfl | rfl
      · exfalso; exact Nat.not_prime_one hp
      · left; rfl
    · -- case: n | 3
      have h1_or_3 : n = 1 ∨ n = 3 :=
        (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd
      rcases h1_or_3 with rfl | rfl
      · exfalso; exact Nat.not_prime_one hp
      · right; left; rfl
    · -- case: n | 5
      have h1_or_5 : n = 1 ∨ n = 5 :=
        (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd
      rcases h1_or_5 with rfl | rfl
      · exfalso; exact Nat.not_prime_one hp
      · right; right; rfl
  · -- 右から左への証明: n ∈ {2, 3, 5} ならば サポートに含まれる
    intro h
    rcases h with rfl | rfl | rfl
    · exact Or.inl ⟨by decide, dvd_refl 2⟩
    · exact Or.inr (Or.inl ⟨by decide, dvd_refl 3⟩)
    · exact Or.inr (Or.inr ⟨by decide, dvd_refl 5⟩)

private lemma univ_twoThreeFiveTriple_support :
    (Finset.univ : Finset twoThreeFiveTriple.support) =
      ({⟨2, by exact (mem_twoThreeFiveTriple_support_iff 2).2 (Or.inl rfl)⟩,
        ⟨3, by exact (mem_twoThreeFiveTriple_support_iff 3).2 (Or.inr (Or.inl rfl))⟩,
        ⟨5, by exact (mem_twoThreeFiveTriple_support_iff 5).2 (Or.inr (Or.inr rfl))⟩} :
          Finset twoThreeFiveTriple.support) := by
  ext p
  rcases p with ⟨n, hn⟩
  constructor
  · intro _
    have hmem : n = 2 ∨ n = 3 ∨ n = 5 :=
      (mem_twoThreeFiveTriple_support_iff n).1 hn
    rcases hmem with rfl | rfl | rfl
    · simp
    · simp
    · simp
  · intro _
    simp

private lemma sum_univ_twoThreeFiveTriple_support
    (f : twoThreeFiveTriple.support → ℤ) :
    (∑ p : twoThreeFiveTriple.support, f p) =
      f ⟨2, by exact (mem_twoThreeFiveTriple_support_iff 2).2 (Or.inl rfl)⟩ +
      f ⟨3, by exact (mem_twoThreeFiveTriple_support_iff 3).2 (Or.inr (Or.inl rfl))⟩ +
      f ⟨5, by exact (mem_twoThreeFiveTriple_support_iff 5).2 (Or.inr (Or.inr rfl))⟩ := by
  rw [univ_twoThreeFiveTriple_support]
  simp [add_assoc]

/-- The transported tangent has formal derivative `1` on `2`. -/
lemma kernelTangent235OnTriple_formalDeriv_two :
    ABD.formalDeriv twoThreeFiveTriple.support kernelTangent235OnTriple
        twoThreeFiveTriple.a = 1 := by
  unfold ABD.formalDeriv
  rw [sum_univ_twoThreeFiveTriple_support]
  simp [
    twoThreeFiveTriple,
    ABD.derivCoeff,
    ABD.val,
    kernelTangent235OnTriple,
    kernelTangent235_nat
  ]

/-- The transported tangent has formal derivative `0` on `3`. -/
lemma kernelTangent235OnTriple_formalDeriv_three :
    ABD.formalDeriv twoThreeFiveTriple.support kernelTangent235OnTriple
        twoThreeFiveTriple.b = 0 := by
  unfold ABD.formalDeriv
  rw [sum_univ_twoThreeFiveTriple_support]
  simp [
    twoThreeFiveTriple,
    ABD.derivCoeff,
    ABD.val,
    kernelTangent235OnTriple,
    kernelTangent235_nat
  ]

/-- The transported tangent has formal derivative `1` on `5`. -/
lemma kernelTangent235OnTriple_formalDeriv_five :
    ABD.formalDeriv twoThreeFiveTriple.support kernelTangent235OnTriple
        twoThreeFiveTriple.c = 1 := by
  unfold ABD.formalDeriv
  rw [sum_univ_twoThreeFiveTriple_support]
  simp [
    twoThreeFiveTriple,
    ABD.derivCoeff,
    ABD.val,
    kernelTangent235OnTriple,
    kernelTangent235_nat
  ]

/-- The transported concrete tangent satisfies the additive constraint on the
canonical support of the triple `2 + 3 = 5`.
-/
theorem kernelTangent235OnTriple_additive :
    ABD.AdditiveOn twoThreeFiveTriple.support kernelTangent235OnTriple
      twoThreeFiveTriple.a twoThreeFiveTriple.b twoThreeFiveTriple.c := by
  unfold ABD.AdditiveOn
  rw [
    kernelTangent235OnTriple_formalDeriv_two,
    kernelTangent235OnTriple_formalDeriv_three,
    kernelTangent235OnTriple_formalDeriv_five
  ]
  simp

/-- The transported concrete tangent is nonzero on the canonical triple support. -/
theorem kernelTangent235OnTriple_nondegenerate :
    ABD.Nondegenerate twoThreeFiveTriple.support kernelTangent235OnTriple := by
  unfold ABD.Nondegenerate
  refine ⟨⟨2, by exact (mem_twoThreeFiveTriple_support_iff 2).2 (Or.inl rfl)⟩, ?_⟩
  simp [kernelTangent235OnTriple, kernelTangent235_nat]

/-- The transported concrete tangent is coordinatewise small with bound `1`. -/
theorem kernelTangent235OnTriple_small_one :
    ABD.SmallTangent twoThreeFiveTriple.support kernelTangent235OnTriple 1 := by
  unfold ABD.SmallTangent ABD.CoordinateBounded
  intro hp
  rcases hp with ⟨n, hn⟩
  have hmem : n = 2 ∨ n = 3 ∨ n = 5 :=
    (mem_twoThreeFiveTriple_support_iff n).1 hn
  rcases hmem with rfl | rfl | rfl
  · simp [kernelTangent235OnTriple, kernelTangent235_nat]
  · simp [kernelTangent235OnTriple, kernelTangent235_nat]
  · simp [kernelTangent235OnTriple, kernelTangent235_nat]

/-- The transported concrete tangent as a small Pasten candidate on the actual
`ABCTriple.support` for `2 + 3 = 5`.
-/
def concreteSmallPastenCandidate235 :
    ABD.SmallPastenCandidate twoThreeFiveTriple 1 where
  x := kernelTangent235OnTriple
  additive := kernelTangent235OnTriple_additive
  nondegenerate := kernelTangent235OnTriple_nondegenerate
  small := kernelTangent235OnTriple_small_one

/-- The same object after packaging the theoremized Leibniz facts explicitly. -/
def concreteSmallPastenStyleDerivative235 :
    ABD.SmallPastenStyleDerivative twoThreeFiveTriple 1 :=
  concreteSmallPastenCandidate235.toSmallPastenStyleDerivative

/-- Existence form: the actual triple `2 + 3 = 5` has a nonzero small
Pasten-style derivative candidate in the current ABD sense.
-/
theorem exists_concreteSmallPastenStyleDerivative235 :
    ∃ h : ABD.SmallPastenStyleDerivative twoThreeFiveTriple 1,
      h.x = kernelTangent235OnTriple := by
  exact ⟨concreteSmallPastenStyleDerivative235, rfl⟩

end ABD.Examples
