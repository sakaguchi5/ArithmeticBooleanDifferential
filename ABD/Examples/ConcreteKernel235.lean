import Mathlib.Data.Nat.Factorization.Basic
import ABD.Examples.TwoThreeFive
import ABD.Lattice.All

namespace ABD.Examples

/-- A concrete nonzero tangent on the toy support `{2, 3, 5}`.

It is chosen so that the additive constraint for `2 + 3 = 5` is satisfied:
`x₂ = 1`, `x₃ = 0`, and `x₅ = 1`.
-/
def kernelTangent235_nat : ℕ → ℤ :=
  fun n => if n = 2 then 1 else if n = 5 then 1 else 0

/-- The same concrete tangent, restricted to the support `S235`. -/
def kernelTangent235 : ABD.Tangent S235 :=
  fun hp => kernelTangent235_nat hp.1
/-
9個の具体補題の「数学的理由」を2種類に圧縮する
今後の設計にもよるがもっと下層におくべき
-/
private lemma factorization_prime_self {p : ℕ} (hp : Nat.Prime p) :
    (Nat.factorization p) p = 1 :=
  Nat.Prime.factorization_self hp

private lemma factorization_prime_other {n p : ℕ} (h : ¬ p ∣ n) :
    (Nat.factorization n) p = 0 :=
  Nat.factorization_eq_zero_of_not_dvd h

@[simp] private lemma factorization_2_2 :
    (Nat.factorization 2) 2 = 1 :=
  factorization_prime_self (by decide : Nat.Prime 2)

@[simp] private lemma factorization_2_3 :
    (Nat.factorization 2) 3 = 0 :=
  factorization_prime_other (by decide : ¬ 3 ∣ 2)

@[simp] private lemma factorization_2_5 :
    (Nat.factorization 2) 5 = 0 :=
  factorization_prime_other (by decide : ¬ 5 ∣ 2)

@[simp] private lemma factorization_3_2 :
    (Nat.factorization 3) 2 = 0 :=
  factorization_prime_other (by decide : ¬ 2 ∣ 3)

@[simp] private lemma factorization_3_3 :
    (Nat.factorization 3) 3 = 1 :=
  factorization_prime_self (by decide : Nat.Prime 3)

@[simp] private lemma factorization_3_5 :
    (Nat.factorization 3) 5 = 0 :=
  factorization_prime_other (by decide : ¬ 5 ∣ 3)

@[simp] private lemma factorization_5_2 :
    (Nat.factorization 5) 2 = 0 :=
  factorization_prime_other (by decide : ¬ 2 ∣ 5)

@[simp] private lemma factorization_5_3 :
    (Nat.factorization 5) 3 = 0 :=
  factorization_prime_other (by decide : ¬ 3 ∣ 5)

@[simp] private lemma factorization_5_5 :
    (Nat.factorization 5) 5 = 1 :=
  factorization_prime_self (by decide : Nat.Prime 5)

private lemma mem_S235_iff (n : ℕ) :
    n ∈ S235 ↔ n = 2 ∨ n = 3 ∨ n = 5 := by
  simp only [S235, Finset.mem_insert, Finset.mem_singleton]

private lemma univ_S235 :
    (Finset.univ : Finset S235) =
      ({⟨2, by simp [S235]⟩,
        ⟨3, by simp [S235]⟩,
        ⟨5, by simp [S235]⟩} : Finset S235) := by
  ext p
  rcases p with ⟨n, hn⟩
  constructor
  · intro _
    have hmem : n = 2 ∨ n = 3 ∨ n = 5 :=
      (mem_S235_iff n).1 hn
    rcases hmem with rfl | rfl | rfl
    · simp
    · simp
    · simp
  · intro _
    simp

private lemma sum_univ_S235 (f : S235 → ℤ) :
    (∑ p : S235, f p) =
      f ⟨2, by simp [S235]⟩ +
      f ⟨3, by simp [S235]⟩ +
      f ⟨5, by simp [S235]⟩ := by
  rw [univ_S235]
  simp [add_assoc]

/-- The formal derivative of `2` at the concrete tangent. -/
lemma kernelTangent235_formalDeriv_two :
    ABD.formalDeriv S235 kernelTangent235 2 = 1 := by
  unfold ABD.formalDeriv
  rw [sum_univ_S235]
  simp [
    ABD.derivCoeff,
    ABD.val,
    kernelTangent235,
    kernelTangent235_nat
  ]

/-- The formal derivative of `3` at the concrete tangent. -/
lemma kernelTangent235_formalDeriv_three :
    ABD.formalDeriv S235 kernelTangent235 3 = 0 := by
  unfold ABD.formalDeriv
  rw [sum_univ_S235]
  simp [
    ABD.derivCoeff,
    ABD.val,
    kernelTangent235,
    kernelTangent235_nat
  ]

/-- The formal derivative of `5` at the concrete tangent. -/
lemma kernelTangent235_formalDeriv_five :
    ABD.formalDeriv S235 kernelTangent235 5 = 1 := by
  unfold ABD.formalDeriv
  rw [sum_univ_S235]
  simp [
    ABD.derivCoeff,
    ABD.val,
    kernelTangent235,
    kernelTangent235_nat
  ]

/-- The concrete tangent satisfies the additive constraint for `2 + 3 = 5` on
our hand-written support `{2, 3, 5}`. -/
theorem kernelTangent235_additive :
    ABD.AdditiveOn S235 kernelTangent235 2 3 5 := by
  unfold ABD.AdditiveOn
  rw [
    kernelTangent235_formalDeriv_two,
    kernelTangent235_formalDeriv_three,
    kernelTangent235_formalDeriv_five
  ]
  simp

/-- The concrete tangent is a point of the additive-kernel submodule for
`2 + 3 = 5` on the hand-written support `{2, 3, 5}`. -/
theorem kernelTangent235_mem_additiveKernelSubmodule :
    kernelTangent235 ∈ ABD.AdditiveKernelSubmodule S235 2 3 5 := by
  rw [ABD.mem_additiveKernelSubmodule_iff]
  exact kernelTangent235_additive

/-- The concrete tangent is nonzero. -/
theorem kernelTangent235_ne_zero :
    kernelTangent235 ≠ 0 := by
  intro h
  have h2 :=
    congrArg
      (fun x : ABD.Tangent S235 => x ⟨2, by simp [S235]⟩)
      h
  simp [kernelTangent235, kernelTangent235_nat] at h2

/-- The concrete kernel point is nondegenerate for the current minimal
nondegeneracy predicate, because its `2`-coordinate is nonzero. -/
theorem kernelTangent235_nondegenerate :
    ABD.Nondegenerate S235 kernelTangent235 := by
  unfold ABD.Nondegenerate
  refine ⟨⟨2, by simp [S235]⟩, ?_⟩
  simp [kernelTangent235, kernelTangent235_nat]

/-- The concrete kernel point is coordinatewise small with bound `1`. -/
theorem kernelTangent235_small_one :
    ABD.SmallTangent S235 kernelTangent235 1 := by
  unfold ABD.SmallTangent ABD.CoordinateBounded
  intro hp
  rcases hp with ⟨n, hn⟩
  have hmem : n = 2 ∨ n = 3 ∨ n = 5 :=
    (mem_S235_iff n).1 hn
  rcases hmem with rfl | rfl | rfl
  · simp [kernelTangent235, kernelTangent235_nat]
  · simp [kernelTangent235, kernelTangent235_nat]
  · simp [kernelTangent235, kernelTangent235_nat]

/-- The same smallness fact in absolute-value form. -/
theorem kernelTangent235_abs_small_one :
    ABD.CoordinateAbsBounded S235 kernelTangent235 1 := by
  simpa using
    ((ABD.coordinateAbsBounded_iff_smallTangent S235 kernelTangent235 1).2
      kernelTangent235_small_one)

private def unitTangentWeight235 : ABD.TangentWeight S235 :=
  fun _ => 1

/-- The same point is small for the unit weighted predicate. -/
theorem kernelTangent235_unitWeighted_small_one :
    ABD.WeightedSmallTangent S235 unitTangentWeight235 kernelTangent235 1 := by
  unfold ABD.WeightedSmallTangent
  intro hp
  rcases hp with ⟨n, hn⟩
  have hmem : n = 2 ∨ n = 3 ∨ n = 5 :=
    (mem_S235_iff n).1 hn
  rcases hmem with rfl | rfl | rfl
  · simp [unitTangentWeight235, kernelTangent235, kernelTangent235_nat]
    rfl
  · simp [unitTangentWeight235, kernelTangent235, kernelTangent235_nat]
  · simp [unitTangentWeight235, kernelTangent235, kernelTangent235_nat]
    rfl

/-- A concrete bundled package: a nonzero, small point of the additive-kernel
submodule for the toy support `{2, 3, 5}`. -/
structure ConcreteSmallKernelPoint235 where
  x : ABD.Tangent S235
  mem_kernel : x ∈ ABD.AdditiveKernelSubmodule S235 2 3 5
  nondegenerate : ABD.Nondegenerate S235 x
  small : ABD.SmallTangent S235 x 1

/-- The explicit small nondegenerate kernel point for `2 + 3 = 5`. -/
def concreteSmallKernelPoint235 : ConcreteSmallKernelPoint235 where
  x := kernelTangent235
  mem_kernel := kernelTangent235_mem_additiveKernelSubmodule
  nondegenerate := kernelTangent235_nondegenerate
  small := kernelTangent235_small_one

/-- Existence form of the concrete small kernel point. -/
theorem exists_concreteSmallKernelPoint235 :
    ∃ x : ABD.Tangent S235,
      x ∈ ABD.AdditiveKernelSubmodule S235 2 3 5 ∧
      ABD.Nondegenerate S235 x ∧
      ABD.SmallTangent S235 x 1 := by
  exact ⟨kernelTangent235, kernelTangent235_mem_additiveKernelSubmodule,
    kernelTangent235_nondegenerate, kernelTangent235_small_one⟩

end ABD.Examples
