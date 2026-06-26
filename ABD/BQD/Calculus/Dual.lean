import ABD.BQD.Calculus.CarryShift

namespace ABD
namespace BQD
namespace Decomp

variable {α : Type u} [DecidableEq α]

/-- Left-right dual of a BQD decomposition.

This swaps the two active sets while keeping the common universe fixed.
It is different from `Mirror`: mirror moves positions inside the universe,
whereas duality only exchanges the left and right objects. -/
def swap (D : Decomp α) : Decomp α where
  U := D.U
  L := D.R
  R := D.L
  hL := D.hR
  hR := D.hL

@[simp] theorem swap_U (D : Decomp α) :
    D.swap.U = D.U := rfl

@[simp] theorem swap_L (D : Decomp α) :
    D.swap.L = D.R := rfl

@[simp] theorem swap_R (D : Decomp α) :
    D.swap.R = D.L := rfl

@[simp] theorem swap_hL (D : Decomp α) :
    D.swap.hL = D.hR := rfl

@[simp] theorem swap_hR (D : Decomp α) :
    D.swap.hR = D.hL := rfl

/-- Swapping left and right twice returns the original decomposition. -/
@[simp] theorem swap_swap (D : Decomp α) :
    D.swap.swap = D := by
  cases D
  rfl

/-- The both-active atom is invariant under left-right duality. -/
@[simp] theorem swap_B (D : Decomp α) :
    D.swap.B = D.B := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [swap, B, hxL, hxR]

/-- The left-only atom of the dual is the original right-only atom. -/
@[simp] theorem swap_LO (D : Decomp α) :
    D.swap.LO = D.RO := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [swap, LO, RO, hxL, hxR]

/-- The right-only atom of the dual is the original left-only atom. -/
@[simp] theorem swap_RO (D : Decomp α) :
    D.swap.RO = D.LO := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [swap, LO, RO, hxL, hxR]

/-- The neither-active atom is invariant under left-right duality. -/
@[simp] theorem swap_N (D : Decomp α) :
    D.swap.N = D.N := by
  ext x
  by_cases hxU : x ∈ D.U <;>
  by_cases hxL : x ∈ D.L <;>
  by_cases hxR : x ∈ D.R <;>
    simp [swap, N, hxU, hxL, hxR]

/-- The active union is invariant under left-right duality. -/
@[simp] theorem swap_active (D : Decomp α) :
    D.swap.active = D.active := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [swap, active, hxL, hxR]

/-- The exclusive-active region is invariant under left-right duality. -/
@[simp] theorem swap_exclusive (D : Decomp α) :
    D.swap.exclusive = D.exclusive := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [swap, exclusive, LO, RO, hxL, hxR]

/-- `B` count is invariant under left-right duality. -/
@[simp] theorem swap_bCount (D : Decomp α) :
    D.swap.bCount = D.bCount := by
  simp [bCount,Finset.inter_comm]

/-- `LO` count of the dual is the original `RO` count. -/
@[simp] theorem swap_loCount (D : Decomp α) :
    D.swap.loCount = D.roCount := by
  simp [loCount, roCount]

/-- `RO` count of the dual is the original `LO` count. -/
@[simp] theorem swap_roCount (D : Decomp α) :
    D.swap.roCount = D.loCount := by
  simp [loCount, roCount]

/-- `N` count is invariant under left-right duality. -/
@[simp] theorem swap_nCount (D : Decomp α) :
    D.swap.nCount = D.nCount := by
  simp [nCount,Finset.union_comm]

/-- Xor count is invariant under left-right duality. -/
@[simp] theorem swap_xorCount (D : Decomp α) :
    D.swap.xorCount = D.xorCount := by
  simp [xorCount, Nat.add_comm]

/-- Hamming distance is invariant under left-right duality. -/
@[simp] theorem swap_hammingDistance (D : Decomp α) :
    D.swap.hammingDistance = D.hammingDistance := by
  simp [hammingDistance,Nat.add_comm]

/-- Common-active count is invariant under left-right duality. -/
@[simp] theorem swap_commonCount (D : Decomp α) :
    D.swap.commonCount = D.commonCount := by
  simp [commonCount,Finset.inter_comm]

/-- Union-active count is invariant under left-right duality. -/
@[simp] theorem swap_unionCount (D : Decomp α) :
    D.swap.unionCount = D.unionCount := by
  simp [unionCount,Finset.union_comm]

/-- Generate is invariant under left-right duality. -/
@[simp] theorem swap_Generate (D : Decomp α) :
    D.swap.Generate = D.Generate := by
  simp [Generate,Finset.inter_comm]

/-- Propagate is invariant under left-right duality. -/
@[simp] theorem swap_Propagate (D : Decomp α) :
    D.swap.Propagate = D.Propagate := by
  ext x
  by_cases hxL : x ∈ D.L <;> by_cases hxR : x ∈ D.R <;>
    simp [swap, Propagate, LO, RO, hxL, hxR]

/-- Kill is invariant under left-right duality. -/
@[simp] theorem swap_Kill (D : Decomp α) :
    D.swap.Kill = D.Kill := by
  simp [Kill,Finset.union_comm]

/-- Sum without incoming carry is invariant under left-right duality. -/
@[simp] theorem swap_SumNoCarry (D : Decomp α) :
    D.swap.SumNoCarry = D.SumNoCarry := by
  simp [SumNoCarry,Finset.union_comm]

/-- The local carry step is invariant under left-right duality. -/
@[simp] theorem swap_carryStep (D : Decomp α) (incoming : Finset α) :
    D.swap.carryStep incoming = D.carryStep incoming := by
  calc
    D.swap.carryStep incoming
        = D.swap.Generate ∪ (D.swap.Propagate ∩ incoming) := rfl
    _ = D.Generate ∪ (D.Propagate ∩ incoming) := by
        rw [D.swap_Generate, D.swap_Propagate]
    _ = D.carryStep incoming := rfl

/-- The shifted carry step is invariant under left-right duality. -/
@[simp] theorem swap_shiftedCarryStep
    (D : Decomp α) (σ : CarryShift α D.U) (incoming : Finset α) :
    D.swap.shiftedCarryStep σ incoming = D.shiftedCarryStep σ incoming := by
  calc
    D.swap.shiftedCarryStep σ incoming
        = σ.image (D.swap.carryStep incoming) := rfl
    _ = σ.image (D.carryStep incoming) := by
        rw [D.swap_carryStep incoming]
    _ = D.shiftedCarryStep σ incoming := rfl

end Decomp
end BQD
end ABD
