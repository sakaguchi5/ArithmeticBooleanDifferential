import ABD.ABD2.Pasten.Blocks

namespace ABD2
namespace ABCTriple

/-- Pasten additivity condition on the full Boolean support. -/
def AdditiveOn (T : ABCTriple) (x : T.FullTangent) : Prop :=
  formalDeriv T.support x T.a + formalDeriv T.support x T.b =
    formalDeriv T.support x T.c

/-- The Pasten tangent module, presented as a kernel-like predicate. -/
def PastenT (T : ABCTriple) : Set T.FullTangent :=
  {x | T.AdditiveOn x}

/-- The `a` derivative only sees the `a` mask. -/
theorem formalDeriv_a_eq_maskA
    (T : ABCTriple) (x : T.FullTangent) :
    formalDeriv T.support (T.maskA x) T.a = formalDeriv T.support x T.a := by
  exact formalDeriv_eq_PrimeSupport_mask T.support x T.a

/-- The `b` derivative only sees the `b` mask. -/
theorem formalDeriv_b_eq_maskB
    (T : ABCTriple) (x : T.FullTangent) :
    formalDeriv T.support (T.maskB x) T.b = formalDeriv T.support x T.b := by
  exact formalDeriv_eq_PrimeSupport_mask T.support x T.b

/-- The `c` derivative only sees the `c` mask. -/
theorem formalDeriv_c_eq_maskC
    (T : ABCTriple) (x : T.FullTangent) :
    formalDeriv T.support (T.maskC x) T.c = formalDeriv T.support x T.c := by
  exact formalDeriv_eq_PrimeSupport_mask T.support x T.c

/-- Block-balance form of Pasten additivity. -/
def BlockBalance (T : ABCTriple) (x : T.FullTangent) : Prop :=
  formalDeriv T.support (T.maskA x) T.a +
    formalDeriv T.support (T.maskB x) T.b =
      formalDeriv T.support (T.maskC x) T.c

/-- Pasten additivity is equivalent to Boolean block balance. -/
theorem additiveOn_iff_blockBalance
    (T : ABCTriple) (x : T.FullTangent) :
    T.AdditiveOn x ↔ T.BlockBalance x := by
  unfold AdditiveOn BlockBalance
  rw [T.formalDeriv_a_eq_maskA x]
  rw [T.formalDeriv_b_eq_maskB x]
  rw [T.formalDeriv_c_eq_maskC x]

@[simp]
theorem mem_PastenT_iff_blockBalance
    (T : ABCTriple) (x : T.FullTangent) :
    x ∈ T.PastenT ↔ T.BlockBalance x := by
  exact T.additiveOn_iff_blockBalance x

end ABCTriple
end ABD2
