import ABD.Lattice.TripleKernel
import ABD.Lattice.AdditiveLinearFormLinear

namespace ABD

/-- The zero tangent vector belongs to every additive kernel. -/
theorem zeroTangent_mem_additiveKernel
    (S : Finset ℕ) (a b c : ℕ) :
    zeroTangent S ∈ AdditiveKernel S a b c := by
  rw [mem_additiveKernel_iff]
  exact additiveOn_zeroTangent S a b c

/-- Additive kernels are closed under addition of tangent vectors. -/
theorem add_mem_additiveKernel
    {S : Finset ℕ} {a b c : ℕ} {x y : Tangent S}
    (hx : x ∈ AdditiveKernel S a b c)
    (hy : y ∈ AdditiveKernel S a b c) :
    x + y ∈ AdditiveKernel S a b c := by
  rw [mem_additiveKernel_iff] at hx hy ⊢
  rw [additiveOn_iff_linearForm_zero] at hx hy ⊢
  rw [additiveLinearForm_add]
  simp [hx, hy]

/-- Additive kernels are closed under negation of tangent vectors. -/
theorem neg_mem_additiveKernel
    {S : Finset ℕ} {a b c : ℕ} {x : Tangent S}
    (hx : x ∈ AdditiveKernel S a b c) :
    -x ∈ AdditiveKernel S a b c := by
  rw [mem_additiveKernel_iff] at hx ⊢
  rw [additiveOn_iff_linearForm_zero] at hx ⊢
  rw [additiveLinearForm_neg]
  simp [hx]

/-- Additive kernels are closed under integer scalar multiplication. -/
theorem zsmul_mem_additiveKernel
    {S : Finset ℕ} {a b c : ℕ} (k : ℤ) {x : Tangent S}
    (hx : x ∈ AdditiveKernel S a b c) :
    k • x ∈ AdditiveKernel S a b c := by
  rw [mem_additiveKernel_iff] at hx ⊢
  rw [additiveOn_iff_linearForm_zero] at hx ⊢
  rw [additiveLinearForm_zsmul]
  simp [hx]

/-- The zero tangent vector belongs to the additive kernel of every triple. -/
theorem zeroTangent_mem_tripleAdditiveKernel
    (T : ABCTriple) :
    zeroTangent T.support ∈ TripleAdditiveKernel T := by
  rw [mem_tripleAdditiveKernel_iff]
  exact additiveOn_zeroTangent T.support T.a T.b T.c

/-- Triple additive kernels are closed under addition of tangent vectors. -/
theorem add_mem_tripleAdditiveKernel
    {T : ABCTriple} {x y : Tangent T.support}
    (hx : x ∈ TripleAdditiveKernel T)
    (hy : y ∈ TripleAdditiveKernel T) :
    x + y ∈ TripleAdditiveKernel T := by
  exact add_mem_additiveKernel
    (S := T.support) (a := T.a) (b := T.b) (c := T.c) hx hy

/-- Triple additive kernels are closed under negation of tangent vectors. -/
theorem neg_mem_tripleAdditiveKernel
    {T : ABCTriple} {x : Tangent T.support}
    (hx : x ∈ TripleAdditiveKernel T) :
    -x ∈ TripleAdditiveKernel T := by
  exact neg_mem_additiveKernel
    (S := T.support) (a := T.a) (b := T.b) (c := T.c) hx

/-- Triple additive kernels are closed under integer scalar multiplication. -/
theorem zsmul_mem_tripleAdditiveKernel
    {T : ABCTriple} (k : ℤ) {x : Tangent T.support}
    (hx : x ∈ TripleAdditiveKernel T) :
    k • x ∈ TripleAdditiveKernel T := by
  exact zsmul_mem_additiveKernel
    (S := T.support) (a := T.a) (b := T.b) (c := T.c) k hx

end ABD
