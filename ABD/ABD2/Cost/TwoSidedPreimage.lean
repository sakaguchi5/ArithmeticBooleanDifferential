import ABD.ABD2.Cost.SupportRankObstruction
import ABD.ABD2.Cost.TwoSidedHardness

namespace ABD2
namespace ABCTriple

/-- A-side smallness used by the D1 preimage layer.

This measures only the A-mask of a full tangent.  The object still lives in the
ambient full tangent module, so later mask-gluing lemmas can connect it back to
the existing B1/C1 cost predicates without introducing a separate `ATangent`
type. -/
def APreimageSmall
    (T : ABCTriple) (x : T.FullTangent) (B : ℤ) : Prop :=
  T.SmallTangent (T.maskA x) B

/-- B-side smallness used by the D1 preimage layer. -/
def BPreimageSmall
    (T : ABCTriple) (x : T.FullTangent) (B : ℤ) : Prop :=
  T.SmallTangent (T.maskB x) B

/-- D1-A: scalar preimage cost for the A-block linear value. -/
def APreimageCostAtMost
    (T : ABCTriple) (t B : ℤ) : Prop :=
  BlockPreimageCostAtMost T.ADerivValue T.APreimageSmall t B

/-- D1-B: scalar preimage cost for the B-block linear value. -/
def BPreimageCostAtMost
    (T : ABCTriple) (t B : ℤ) : Prop :=
  BlockPreimageCostAtMost T.BDerivValue T.BPreimageSmall t B

/-- Constructor for A-side preimage cost. -/
theorem aPreimageCostAtMost_of_witness
    (T : ABCTriple) {t B : ℤ} {x : T.FullTangent}
    (hvalue : T.ADerivValue x = t)
    (hsmall : T.APreimageSmall x B) :
    T.APreimageCostAtMost t B := by
  exact blockPreimageCostAtMost_of_witness hvalue hsmall

/-- Constructor for B-side preimage cost. -/
theorem bPreimageCostAtMost_of_witness
    (T : ABCTriple) {t B : ℤ} {x : T.FullTangent}
    (hvalue : T.BDerivValue x = t)
    (hsmall : T.BPreimageSmall x B) :
    T.BPreimageCostAtMost t B := by
  exact blockPreimageCostAtMost_of_witness hvalue hsmall

/-- Witness form of A-side preimage cost. -/
theorem exists_witness_of_aPreimageCostAtMost
    (T : ABCTriple) {t B : ℤ}
    (h : T.APreimageCostAtMost t B) :
    ∃ x : T.FullTangent,
      T.ADerivValue x = t ∧ T.APreimageSmall x B := by
  exact h

/-- Witness form of B-side preimage cost. -/
theorem exists_witness_of_bPreimageCostAtMost
    (T : ABCTriple) {t B : ℤ}
    (h : T.BPreimageCostAtMost t B) :
    ∃ x : T.FullTangent,
      T.BDerivValue x = t ∧ T.BPreimageSmall x B := by
  exact h

/-- Independent A/B preimage-cost formulation for a two-sided cancellation scalar.

This is the literal D1 cost split:

* A realizes `t` at bound `BA`;
* B realizes `-t` at bound `BB`;
* the component bounds aggregate to the ambient bound `B`.

The A and B witnesses are intentionally allowed to be different here.  A later
mask-gluing theorem should turn this independent formulation into the same-witness
form below. -/
def TwoSidedSeparatePreimageCostAtMostWith
    (T : ABCTriple) (agg : BoundAggregator) (t B : ℤ) : Prop :=
  t ≠ 0 ∧
    ∃ BA BB : ℤ,
      T.APreimageCostAtMost t BA ∧
        T.BPreimageCostAtMost (-t) BB ∧
          agg BA BB B

/-- Max-aggregated independent A/B preimage cost. -/
def TwoSidedSeparatePreimageCostAtMost
    (T : ABCTriple) (t B : ℤ) : Prop :=
  T.TwoSidedSeparatePreimageCostAtMostWith MaxAgg t B

/-- Same-witness A/B preimage-cost formulation.

This is stronger than `TwoSidedSeparatePreimageCostAtMostWith`: the same full
tangent realizes both the A-value `t` and the B-value `-t`.  This is the right
intermediate object for connecting back to `TwoSidedScalarCancellationCostAtMost`. -/
def TwoSidedScalarPreimageCostAtMostWith
    (T : ABCTriple) (agg : BoundAggregator) (t B : ℤ) : Prop :=
  t ≠ 0 ∧
    ∃ x : T.FullTangent,
    ∃ BA BB : ℤ,
      T.ADerivValue x = t ∧
        T.BDerivValue x = -t ∧
          T.APreimageSmall x BA ∧
            T.BPreimageSmall x BB ∧
              agg BA BB B

/-- Max-aggregated same-witness A/B preimage cost. -/
def TwoSidedScalarPreimageCostAtMost
    (T : ABCTriple) (t B : ℤ) : Prop :=
  T.TwoSidedScalarPreimageCostAtMostWith MaxAgg t B

/-- Same-witness preimage cost forgets to the independent split formulation. -/
theorem twoSidedSeparatePreimageCostAtMostWith_of_scalarPreimageCostAtMostWith
    (T : ABCTriple) (agg : BoundAggregator) {t B : ℤ}
    (h : T.TwoSidedScalarPreimageCostAtMostWith agg t B) :
    T.TwoSidedSeparatePreimageCostAtMostWith agg t B := by
  rcases h with ⟨ht_ne, x, BA, BB, hA, hB, hsmallA, hsmallB, hagg⟩
  exact ⟨ht_ne, BA, BB,
    T.aPreimageCostAtMost_of_witness hA hsmallA,
    T.bPreimageCostAtMost_of_witness hB hsmallB,
    hagg⟩

/-- Max-aggregated same-witness preimage cost forgets to the max-aggregated
independent split formulation. -/
theorem twoSidedSeparatePreimageCostAtMost_of_scalarPreimageCostAtMost
    (T : ABCTriple) {t B : ℤ}
    (h : T.TwoSidedScalarPreimageCostAtMost t B) :
    T.TwoSidedSeparatePreimageCostAtMost t B := by
  exact T.twoSidedSeparatePreimageCostAtMostWith_of_scalarPreimageCostAtMostWith MaxAgg h

/-- A glue principle for independent A/B preimages.

It says that separately realizing `t` on the A side and `-t` on the B side can be
combined into one full tangent with the same component bounds.  This is deliberately
kept as a bridge predicate: the proof should come from the Boolean mask/direct-sum
layer, not from the cost layer. -/
def TwoSidedPreimageGlue
    (T : ABCTriple) : Prop :=
  ∀ {t BA BB : ℤ},
    T.APreimageCostAtMost t BA →
      T.BPreimageCostAtMost (-t) BB →
        ∃ x : T.FullTangent,
          T.ADerivValue x = t ∧
            T.BDerivValue x = -t ∧
              T.APreimageSmall x BA ∧
                T.BPreimageSmall x BB

/-- Glue turns the independent A/B preimage formulation into the same-witness one. -/
theorem twoSidedScalarPreimageCostAtMostWith_of_separatePreimageCostAtMostWith
    (T : ABCTriple) (agg : BoundAggregator) {t B : ℤ}
    (hglue : T.TwoSidedPreimageGlue)
    (h : T.TwoSidedSeparatePreimageCostAtMostWith agg t B) :
    T.TwoSidedScalarPreimageCostAtMostWith agg t B := by
  rcases h with ⟨ht_ne, BA, BB, hA, hB, hagg⟩
  rcases hglue hA hB with ⟨x, hxA, hxB, hsmallA, hsmallB⟩
  exact ⟨ht_ne, x, BA, BB, hxA, hxB, hsmallA, hsmallB, hagg⟩

/-- Glue turns the max-aggregated independent split formulation into the
max-aggregated same-witness formulation. -/
theorem twoSidedScalarPreimageCostAtMost_of_separatePreimageCostAtMost
    (T : ABCTriple) {t B : ℤ}
    (hglue : T.TwoSidedPreimageGlue)
    (h : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.TwoSidedScalarPreimageCostAtMost t B := by
  exact T.twoSidedScalarPreimageCostAtMostWith_of_separatePreimageCostAtMostWith
    MaxAgg hglue h

/-- Aggregate control bridge from component A/B smallness to the existing AB-smallness
predicate.

This is the second bridge needed to return from the D1 preimage layer to the
already-existing C1 scalar-cancellation cost.  It should later be proved from the
chosen aggregate and the concrete coordinate/gauge smallness properties. -/
def TwoSidedPreimageAggregateControlsABSmall
    (T : ABCTriple) (agg : BoundAggregator) : Prop :=
  ∀ {x : T.FullTangent} {BA BB B : ℤ},
    T.APreimageSmall x BA →
      T.BPreimageSmall x BB →
        agg BA BB B →
          T.ABSmallTangent x B

/-- Same-witness D1 preimage cost gives the old scalar cancellation cost once the
aggregate is known to control the existing AB-smallness predicate. -/
theorem twoSidedScalarCancellationCostAtMost_of_scalarPreimageCostAtMostWith
    (T : ABCTriple) (agg : BoundAggregator) {t B : ℤ}
    (hcontrol : T.TwoSidedPreimageAggregateControlsABSmall agg)
    (h : T.TwoSidedScalarPreimageCostAtMostWith agg t B) :
    T.TwoSidedScalarCancellationCostAtMost t B := by
  rcases h with ⟨ht_ne, x, BA, BB, hA, hB, hsmallA, hsmallB, hagg⟩
  have hcancel : T.ADerivValue x + T.BDerivValue x = 0 := by
    rw [hA, hB]
    simp
  exact ⟨ht_ne, x, hA, hcancel, hcontrol hsmallA hsmallB hagg⟩

/-- Max-aggregated same-witness D1 preimage cost gives the old scalar cancellation
cost under max-aggregate control. -/
theorem twoSidedScalarCancellationCostAtMost_of_scalarPreimageCostAtMost
    (T : ABCTriple) {t B : ℤ}
    (hcontrol : T.TwoSidedPreimageAggregateControlsABSmall MaxAgg)
    (h : T.TwoSidedScalarPreimageCostAtMost t B) :
    T.TwoSidedScalarCancellationCostAtMost t B := by
  exact T.twoSidedScalarCancellationCostAtMost_of_scalarPreimageCostAtMostWith
    MaxAgg hcontrol h

/-- Full route from independent A/B preimage costs to the old scalar cancellation
cost: first glue the A/B witnesses, then use aggregate control to recover
`ABSmallTangent`. -/
theorem twoSidedScalarCancellationCostAtMost_of_separatePreimageCostAtMostWith
    (T : ABCTriple) (agg : BoundAggregator) {t B : ℤ}
    (hglue : T.TwoSidedPreimageGlue)
    (hcontrol : T.TwoSidedPreimageAggregateControlsABSmall agg)
    (h : T.TwoSidedSeparatePreimageCostAtMostWith agg t B) :
    T.TwoSidedScalarCancellationCostAtMost t B := by
  exact T.twoSidedScalarCancellationCostAtMost_of_scalarPreimageCostAtMostWith agg hcontrol
    (T.twoSidedScalarPreimageCostAtMostWith_of_separatePreimageCostAtMostWith agg hglue h)

/-- Max-aggregated full route from independent A/B preimage costs to the old scalar
cancellation cost. -/
theorem twoSidedScalarCancellationCostAtMost_of_separatePreimageCostAtMost
    (T : ABCTriple) {t B : ℤ}
    (hglue : T.TwoSidedPreimageGlue)
    (hcontrol : T.TwoSidedPreimageAggregateControlsABSmall MaxAgg)
    (h : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.TwoSidedScalarCancellationCostAtMost t B := by
  exact T.twoSidedScalarCancellationCostAtMost_of_separatePreimageCostAtMostWith
    MaxAgg hglue hcontrol h

/-- A concrete independent A/B preimage witness at an accepted bound defeats D1
hardness, provided the two bridge principles are available. -/
theorem not_twoSidedABCancellationHardness_of_separatePreimageCostAtMost
    (T : ABCTriple) (R : T.BoundRegime) {t B : ℤ}
    (hB : R.accepts B)
    (hglue : T.TwoSidedPreimageGlue)
    (hcontrol : T.TwoSidedPreimageAggregateControlsABSmall MaxAgg)
    (h : T.TwoSidedSeparatePreimageCostAtMost t B) :
    ¬ T.TwoSidedABCancellationHardness R := by
  exact T.not_twoSidedABCancellationHardness_of_scalarCancellationCostAtMost R hB
    (T.twoSidedScalarCancellationCostAtMost_of_separatePreimageCostAtMost
      hglue hcontrol h)

end ABCTriple
end ABD2
