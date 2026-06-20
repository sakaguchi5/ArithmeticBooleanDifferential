import Mathlib.Data.Nat.Factorization.Basic
import ABD.ABD3.Core.ABCData
import ABD.ABD3.Core.BooleanSupport

namespace ABD3

/-- Prime support extracted from mathlib's factorization map. -/
def primeSupport (n : ℕ) : Support :=
  n.factorization.support

/-- Membership in `primeSupport n` means the corresponding factorization
coefficient is nonzero. -/
theorem factorization_ne_zero_of_mem_primeSupport {n p : ℕ}
    (hp : p ∈ primeSupport n) :
    n.factorization p ≠ 0 := by
  have hp' : p ∈ n.factorization.support := by
    simpa [primeSupport] using hp
  exact Finsupp.mem_support_iff.mp hp'

/-- A prime-support direction actually divides the integer. -/
theorem dvd_of_mem_primeSupport {n p : ℕ}
    (hp : p ∈ primeSupport n) :
    p ∣ n := by
  by_contra hnot
  exact (factorization_ne_zero_of_mem_primeSupport hp)
    (Nat.factorization_eq_zero_of_not_dvd hnot)

/-- The support layer never contains the direction `1`. -/
theorem ne_one_of_mem_primeSupport {n p : ℕ}
    (hp : p ∈ primeSupport n) :
    p ≠ 1 := by
  intro hp_one
  exact (factorization_ne_zero_of_mem_primeSupport hp) (by
    simp [hp_one, Nat.factorization_one_right n])

/-- If two integers are coprime, their prime-support layers are disjoint. -/
theorem not_mem_primeSupport_right_of_coprime
    {m n p : ℕ} (hcop : Nat.Coprime m n)
    (hm : p ∈ primeSupport m) :
    p ∉ primeSupport n := by
  intro hn
  have hpm : p ∣ m := dvd_of_mem_primeSupport hm
  have hpn : p ∣ n := dvd_of_mem_primeSupport hn
  have hpgcd : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm hpn
  have hgcd : Nat.gcd m n = 1 := hcop
  have hp_dvd_one : p ∣ 1 := by
    rw [← hgcd]
    exact hpgcd
  have hp_one : p = 1 := Nat.dvd_one.mp hp_dvd_one
  exact (ne_one_of_mem_primeSupport hm) hp_one

/-- Coprime integers have disjoint prime supports. -/
theorem primeSupport_disjoint_of_coprime
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    Support.Disjoint (primeSupport m) (primeSupport n) := by
  unfold Support.Disjoint
  ext p
  constructor
  · intro hp
    have hm : p ∈ primeSupport m := (Finset.mem_inter.mp hp).1
    have hn : p ∈ primeSupport n := (Finset.mem_inter.mp hp).2
    exact False.elim ((not_mem_primeSupport_right_of_coprime hcop hm) hn)
  · intro hp
    simp at hp

namespace ABCData

/-- A-side prime support. -/
def supportA (T : ABCData) : Support :=
  primeSupport T.A.val

/-- B-side prime support. -/
def supportB (T : ABCData) : Support :=
  primeSupport T.B.val

/-- C-side prime support. -/
def supportC (T : ABCData) : Support :=
  primeSupport T.C.val

/-- Full Boolean support of the triple. -/
def supportABC (T : ABCData) : Support :=
  T.supportA ∪ T.supportB ∪ T.supportC

/-- Boolean block-disjointness for the three prime supports. -/
def SupportBlocksDisjoint (T : ABCData) : Prop :=
  Support.PairwiseDisjoint3 T.supportA T.supportB T.supportC

/-- Boolean partition certificate for the triple support. -/
def SupportBlocksPartition (T : ABCData) : Prop :=
  Support.BlocksPartition T.supportA T.supportB T.supportC T.supportABC

/-- The full support is definitionally the union of the three block supports. -/
theorem supportABC_eq_union (T : ABCData) :
    T.supportABC = T.supportA ∪ T.supportB ∪ T.supportC := by
  rfl

/-- The stored primitive condition. -/
theorem coprimeAB (T : ABCData) :
    Nat.Coprime T.A.val T.B.val :=
  T.h_coprime

/-- In a primitive ABC triple, `A` is also coprime to `C`. -/
theorem coprimeAC (T : ABCData) :
    Nat.Coprime T.A.val T.C.val := by
  rw [← T.h_add]
  exact (Nat.coprime_self_add_right
    (m := T.A.val) (n := T.B.val)).mpr T.h_coprime

/-- In a primitive ABC triple, `B` is also coprime to `C`. -/
theorem coprimeBC (T : ABCData) :
    Nat.Coprime T.B.val T.C.val := by
  rw [← T.h_add]
  exact (Nat.coprime_add_self_right
    (m := T.B.val) (n := T.A.val)).mpr T.h_coprime.symm

/-- The three prime-support blocks of an `ABCData` are pairwise disjoint.

This is no longer an external hypothesis: it follows from `A + B = C`
and the primitive condition stored in `ABCData`. Positivity is part of
the core data, but the disjointness argument is driven by coprimality.
-/
theorem supportBlocksDisjoint (T : ABCData) :
    T.SupportBlocksDisjoint := by
  unfold SupportBlocksDisjoint Support.PairwiseDisjoint3
  exact ⟨
    by
      simpa [supportA, supportB]
        using primeSupport_disjoint_of_coprime T.coprimeAB,
    by
      simpa [supportA, supportC]
        using primeSupport_disjoint_of_coprime T.coprimeAC,
    by
      simpa [supportB, supportC]
        using primeSupport_disjoint_of_coprime T.coprimeBC
  ⟩

/-- The support blocks form a partition of the full support.

The union part is definitional from `supportABC`; the disjointness part
is supplied by `supportBlocksDisjoint`.
-/
theorem supportBlocksPartition (T : ABCData) :
    T.SupportBlocksPartition := by
  exact ⟨rfl, T.supportBlocksDisjoint⟩

/-- A support partition can be built from explicit block-disjointness.

For `ABCData` itself, prefer `supportBlocksPartition`, since block-disjointness
is now derived from the primitive positive triple data.
-/
theorem supportBlocksPartition_of_disjoint
    (T : ABCData) (h : T.SupportBlocksDisjoint) :
    T.SupportBlocksPartition := by
  exact ⟨rfl, h⟩

end ABCData
end ABD3
