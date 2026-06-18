import ABD.ABD.PastenBlock.DerivativeRestriction

namespace ABD

/-- The `c`-side coefficient at a coordinate of `S_c = supp(c)`. -/
def ABCTriple.cCoeff (T : ABCTriple) (hp : {p : ℕ // p ∈ T.supportC}) : ℤ :=
  derivCoeff T.c hp.1

/-- The `c`-side linear form `L_c : ℤ^{S_c} → ℤ`.

This is the adjustment map that tries to absorb the target produced by the
`a/b`-side seed. -/
def ABCTriple.cLinearForm (T : ABCTriple) (xC : T.CTangent) : ℤ :=
  formalDeriv T.supportC xC T.c

/-- The `a/b`-side target that must be absorbed by the `c`-side adjustment map. -/
def ABCTriple.abSeedTarget
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) : ℤ :=
  formalDeriv T.supportA xA T.a + formalDeriv T.supportB xB T.b

/-- The `c`-side linear form written as an explicit coefficient sum. -/
theorem ABCTriple.cLinearForm_eq_sum
    (T : ABCTriple) (xC : T.CTangent) :
    T.cLinearForm xC =
      ∑ hp : {p : ℕ // p ∈ T.supportC}, T.cCoeff hp * xC hp := by
  rfl

/-- The integer image of the `c`-side adjustment map. -/
def ABCTriple.cImage (T : ABCTriple) : Set ℤ :=
  {target | ∃ xC : T.CTangent, T.cLinearForm xC = target}

@[simp]
theorem ABCTriple.mem_cImage_iff (T : ABCTriple) (target : ℤ) :
    target ∈ T.cImage ↔ ∃ xC : T.CTangent, T.cLinearForm xC = target := by
  rfl

/-- The `a/b` seed is adjustable exactly when its target lies in the integer
image of `L_c`. -/
def ABCTriple.CAdjustable
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) : Prop :=
  T.abSeedTarget xA xB ∈ T.cImage

/-- A bundled lift witnessing that the `c`-side can absorb the `a/b` target. -/
structure ABCTriple.CAdjustmentLift
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) where
  xC : T.CTangent
  adjusts : T.cLinearForm xC = T.abSeedTarget xA xB

/-- The adjustment predicate is exactly existence of a `c`-side lift. -/
theorem ABCTriple.cAdjustable_iff_nonempty_lift
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) :
    T.CAdjustable xA xB ↔ Nonempty (T.CAdjustmentLift xA xB) := by
  unfold ABCTriple.CAdjustable
  rw [T.mem_cImage_iff]
  constructor
  · intro h
    rcases h with ⟨xC, hxC⟩
    exact ⟨{ xC := xC, adjusts := hxC }⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.xC, h.adjusts⟩

/-- Pasten's block equation says precisely that the restricted `c`-block is a
lift of the target produced by the restricted `a/b` blocks. -/
theorem ABCTriple.mem_pastenT_iff_restrictC_adjusts_abSeedTarget
    (T : ABCTriple) (x : Tangent T.support) :
    x ∈ PastenT T ↔
      T.cLinearForm (T.restrictC x) =
        T.abSeedTarget (T.restrictA x) (T.restrictB x) := by
  rw [T.mem_pastenT_iff_restrict_block_equation]
  unfold ABCTriple.cLinearForm ABCTriple.abSeedTarget
  constructor
  · intro h
    exact h.symm
  · intro h
    exact h.symm

/-- Any full Pasten tangent determines a `c`-side adjustment for its restricted
`a/b` seed. -/
theorem ABCTriple.cAdjustable_of_mem_pastenT
    (T : ABCTriple) {x : Tangent T.support} (hx : x ∈ PastenT T) :
    T.CAdjustable (T.restrictA x) (T.restrictB x) := by
  unfold ABCTriple.CAdjustable
  rw [T.mem_cImage_iff]
  exact ⟨T.restrictC x,
    (T.mem_pastenT_iff_restrictC_adjusts_abSeedTarget x).1 hx⟩

/-- The same implication in bundled-lift form. -/
def ABCTriple.cAdjustmentLift_of_mem_pastenT
    (T : ABCTriple) {x : Tangent T.support} (hx : x ∈ PastenT T) :
    T.CAdjustmentLift (T.restrictA x) (T.restrictB x) where
  xC := T.restrictC x
  adjusts := (T.mem_pastenT_iff_restrictC_adjusts_abSeedTarget x).1 hx

/-- A `c`-side lift is exactly a solution of the integer image problem for the
seed target. -/
theorem ABCTriple.cAdjustmentLift_iff_target_mem_cImage
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) :
    Nonempty (T.CAdjustmentLift xA xB) ↔ T.abSeedTarget xA xB ∈ T.cImage := by
  rw [← T.cAdjustable_iff_nonempty_lift]
  rfl

end ABD
