import ABD.BQD.Bit.Decomp
import ABD.BQD.Calculus.CarryShift

namespace ABD
namespace BQD
namespace Bit

/-- Bounded upward carry shift inside the common-width bit universe.

Only positions whose successor still lies inside `bitUniverse w` are shifted.
Positions whose successor would leave the common universe are not included here;
they are recorded separately by `overflowCarry`. -/
def shiftUp (w : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (S.filter fun i => i + 1 ∈ bitUniverse w).image fun i => i + 1

/-- A carry overflow occurs when a carry position would shift outside the
common-width bit universe. -/
def overflowCarry (w : ℕ) (S : Finset ℕ) : Prop :=
  ∃ i, i ∈ S ∧ i + 1 ∉ bitUniverse w

/-- No-overflow predicate for bounded carry shifting. -/
def noOverflowCarry (w : ℕ) (S : Finset ℕ) : Prop :=
  ¬ overflowCarry w S

@[simp] theorem mem_shiftUp {w : ℕ} {S : Finset ℕ} {j : ℕ} :
    j ∈ shiftUp w S ↔
      ∃ i, i ∈ S ∧ i + 1 ∈ bitUniverse w ∧ i + 1 = j := by
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, hij⟩
    rcases Finset.mem_filter.mp hi with ⟨hiS, hiU⟩
    exact ⟨i, hiS, hiU, hij⟩
  · intro h
    rcases h with ⟨i, hiS, hiU, hij⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, hiU⟩, hij⟩

/-- Bounded carry shift always lands inside the common-width bit universe. -/
theorem shiftUp_subset_bitUniverse (w : ℕ) (S : Finset ℕ) :
    shiftUp w S ⊆ bitUniverse w := by
  intro j hj
  rcases mem_shiftUp.mp hj with ⟨i, _hiS, hiU, hij⟩
  simpa [hij] using hiU

@[simp] theorem shiftUp_empty (w : ℕ) :
    shiftUp w (∅ : Finset ℕ) = ∅ := by
  ext j
  simp [shiftUp]

/-- No overflow is equivalent to every raw carry position being shiftable. -/
theorem noOverflowCarry_iff_forall_shiftable (w : ℕ) (S : Finset ℕ) :
    noOverflowCarry w S ↔ ∀ i, i ∈ S → i + 1 ∈ bitUniverse w := by
  constructor
  · intro h i hiS
    by_contra hbad
    exact h ⟨i, hiS, hbad⟩
  · intro h hover
    rcases hover with ⟨i, hiS, hbad⟩
    exact hbad (h i hiS)

/-- A convenient way to prove no overflow. -/
theorem noOverflowCarry_of_forall_shiftable
    {w : ℕ} {S : Finset ℕ}
    (h : ∀ i, i ∈ S → i + 1 ∈ bitUniverse w) :
    noOverflowCarry w S := by
  exact (noOverflowCarry_iff_forall_shiftable w S).mpr h

/-- Bounded carry step: apply the local BQD carry rule, then bounded-shift the
raw carry positions inside the common-width bit universe. -/
def boundedCarryStep (w : ℕ) (D : Decomp ℕ) (incoming : Finset ℕ) : Finset ℕ :=
  shiftUp w (D.carryStep incoming)

/-- Overflow predicate for one BQD carry step. -/
def overflowAtStep (w : ℕ) (D : Decomp ℕ) (incoming : Finset ℕ) : Prop :=
  overflowCarry w (D.carryStep incoming)

/-- No-overflow predicate for one BQD carry step. -/
def noOverflowAtStep (w : ℕ) (D : Decomp ℕ) (incoming : Finset ℕ) : Prop :=
  noOverflowCarry w (D.carryStep incoming)

@[simp] theorem boundedCarryStep_def
    (w : ℕ) (D : Decomp ℕ) (incoming : Finset ℕ) :
    boundedCarryStep w D incoming = shiftUp w (D.carryStep incoming) := rfl

/-- Bounded carry steps always remain inside the common-width bit universe. -/
theorem boundedCarryStep_subset_bitUniverse
    (w : ℕ) (D : Decomp ℕ) (incoming : Finset ℕ) :
    boundedCarryStep w D incoming ⊆ bitUniverse w := by
  exact shiftUp_subset_bitUniverse w (D.carryStep incoming)

/-- A bit-level decomp has its raw carry step inside its common-width bit universe. -/
theorem bit_carryStep_subset_bitUniverse
    (w x y : ℕ) (incoming : Finset ℕ) :
    (decomp w x y).carryStep incoming ⊆ bitUniverse w := by
  intro i hi
  have hU : i ∈ (decomp w x y).U :=
    (decomp w x y).carryStep_subset_U incoming hi
  simpa using hU

/-- No overflow at a carry step is equivalent to every raw carry position being
shiftable inside the common-width bit universe. -/
theorem noOverflowAtStep_iff_forall_shiftable
    (w : ℕ) (D : Decomp ℕ) (incoming : Finset ℕ) :
    noOverflowAtStep w D incoming ↔
      ∀ i, i ∈ D.carryStep incoming → i + 1 ∈ bitUniverse w := by
  exact noOverflowCarry_iff_forall_shiftable w (D.carryStep incoming)

/-- A convenient way to prove no overflow at one carry step. -/
theorem noOverflowAtStep_of_forall_shiftable
    {w : ℕ} {D : Decomp ℕ} {incoming : Finset ℕ}
    (h : ∀ i, i ∈ D.carryStep incoming → i + 1 ∈ bitUniverse w) :
    noOverflowAtStep w D incoming := by
  exact (noOverflowAtStep_iff_forall_shiftable w D incoming).mpr h

end Bit
end BQD
end ABD
