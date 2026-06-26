import ABD.BQD.Calculus.Idempotent
import ABD.BQD.Bit.Decomp
import ABD.BQD.Bit.Additive.NormalForm

namespace ABD
namespace BQD
namespace Bit
namespace Additive

/-- Build an additive normal form from any BQD decomposition whose universe is
`bitUniverse width`.

This is the bridge from the abstract two-variable BQD calculus to the
Finset-based additive bit normal form. -/
def ofDecomp (width : ℕ) (D : Decomp ℕ) (hU : D.U = bitUniverse width) :
    NormalForm width where
  B := D.B
  LO := D.LO
  RO := D.RO
  N := D.N
  hB := by
    intro x hx
    rw [← hU]
    exact D.B_subset_U hx
  hLO := by
    intro x hx
    rw [← hU]
    exact D.LO_subset_U hx
  hRO := by
    intro x hx
    rw [← hU]
    exact D.RO_subset_U hx
  hN := by
    intro x hx
    rw [← hU]
    exact D.N_subset_U hx
  hB_LO := D.B_inter_LO_eq_empty
  hB_RO := D.B_inter_RO_eq_empty
  hB_N := D.B_inter_N_eq_empty
  hLO_RO := D.LO_inter_RO_eq_empty
  hLO_N := D.LO_inter_N_eq_empty
  hRO_N := D.RO_inter_N_eq_empty
  hcover := by
    rw [← hU]
    exact D.B_union_LO_union_RO_union_N_eq_U

/-- The additive normal form associated to the bit decomposition of two naturals
at common width `width`. -/
def ofPair (width x y : ℕ) : NormalForm width :=
  ofDecomp width (decomp width x y) rfl

@[simp] theorem ofPair_B (width x y : ℕ) :
    (ofPair width x y).B = (decomp width x y).B := rfl

@[simp] theorem ofPair_LO (width x y : ℕ) :
    (ofPair width x y).LO = (decomp width x y).LO := rfl

@[simp] theorem ofPair_RO (width x y : ℕ) :
    (ofPair width x y).RO = (decomp width x y).RO := rfl

@[simp] theorem ofPair_N (width x y : ℕ) :
    (ofPair width x y).N = (decomp width x y).N := rfl

/-- Soundness specialized to the normal form generated from a bit pair. -/
@[simp] theorem ofPair_add_eq_c (width x y : ℕ) :
    (ofPair width x y).a + (ofPair width x y).b = (ofPair width x y).c := by
  exact NormalForm.add_eq_c (ofPair width x y)

end Additive
end Bit
end BQD
end ABD
