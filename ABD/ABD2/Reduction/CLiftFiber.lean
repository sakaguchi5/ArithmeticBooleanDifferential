import ABD.ABD2.Reduction.CFiber

namespace ABD2
namespace ABCTriple

/-- The fiber of C-lifts over a fixed seed. -/
def CLiftFiber (T : ABCTriple) (seed : T.FullTangent) : Set T.FullTangent :=
  {lift | T.HasCLift seed lift}

@[simp]
theorem mem_CLiftFiber_iff
    (T : ABCTriple) (seed lift : T.FullTangent) :
    lift ∈ T.CLiftFiber seed ↔ T.HasCLift seed lift := by
  rfl

/-- Difference of two points in the same C-lift fiber lies in the C-kernel. -/
theorem sub_mem_CKernel_of_mem_CLiftFiber
    (T : ABCTriple) {seed lift₁ lift₂ : T.FullTangent}
    (h₁ : lift₁ ∈ T.CLiftFiber seed)
    (h₂ : lift₂ ∈ T.CLiftFiber seed) :
    lift₁ - lift₂ ∈ T.CKernel := by
  exact T.sub_mem_CKernel_of_HasCLift_same_seed h₁ h₂

/-- Directions which preserve a C-lift fiber.

A vector in `CKernel` alone is not enough: it could change A/B masks.  The correct
fiber directions are C-kernel vectors with zero A and B masks. -/
def CLiftDirection (T : ABCTriple) (k : T.FullTangent) : Prop :=
  k ∈ T.CKernel ∧ T.maskA k = 0 ∧ T.maskB k = 0

/-- Adding a C-lift direction keeps a point in the same C-lift fiber. -/
theorem add_mem_CLiftFiber_of_CLiftDirection
    (T : ABCTriple) {seed lift k : T.FullTangent}
    (hlift : lift ∈ T.CLiftFiber seed)
    (hk : T.CLiftDirection k) :
    lift + k ∈ T.CLiftFiber seed := by
  change T.HasCLift seed lift at hlift
  rcases hk with ⟨hkC, hkA, hkB⟩
  refine
    { maskA_eq := ?_
      maskB_eq := ?_
      c_balance := ?_ }
  · rw [T.maskA_add lift k]
    rw [hlift.maskA_eq, hkA]
    simp
  · rw [T.maskB_add lift k]
    rw [hlift.maskB_eq, hkB]
    simp
  · rw [T.cLinearForm_add lift k]
    rw [hlift.c_balance]
    have hkzero : T.cLinearForm k = 0 := (T.mem_CKernel_iff k).1 hkC
    rw [hkzero]
    simp

end ABCTriple
end ABD2
