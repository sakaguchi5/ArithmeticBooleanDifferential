import ABD.ABD2.Cost.SectionBridge
import ABD.ABD2.Gauge.Gauge

namespace ABD2
namespace ABCTriple

/-- Gauge version of the pure forced C-lift cost.

This is the same scalar preimage cost as `PureForcedCLiftCostAtMost`, but with an
arbitrary full-tangent gauge replacing the coordinate gauge. -/
def GaugePureForcedCLiftCostAtMost
    (T : ABCTriple) (G : T.Gauge) (t B : ℤ) : Prop :=
  BlockPreimageCostAtMost T.cLinearForm G.small t B

/-- A concrete lift witness gives gauge pure forced C-lift cost. -/
theorem gaugePureForcedCLiftCostAtMost_of_witness
    (T : ABCTriple) (G : T.Gauge) {t B : ℤ} {lift : T.FullTangent}
    (hlinear : T.cLinearForm lift = t)
    (hsmall : G.small lift B) :
    T.GaugePureForcedCLiftCostAtMost G t B := by
  exact blockPreimageCostAtMost_of_witness hlinear hsmall

/-- Gauge version of C2b full one-sided forced cost. -/
def GaugeOneSidedForcedCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (B : ℤ) : Prop :=
  ∃ seed : T.FullTangent,
  ∃ lift : T.FullTangent,
  ∃ t : ℤ,
    t ≠ 0 ∧
    T.OneSidedABSupport ∧
    T.GoodBasePoint P seed ∧
    T.HasCLift seed lift ∧
    T.abTarget seed = t ∧
    T.cLinearForm lift = t ∧
    G.small lift B

/-- Coordinate one-sided forced cost is the coordinate-gauge instance of the
abstract gauge cost. -/
theorem gaugeOneSidedForcedCostAtMost_coordinateGauge_of_oneSidedForcedCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.OneSidedForcedCostAtMost P B) :
    T.GaugeOneSidedForcedCostAtMost P T.coordinateGauge B := by
  rcases h with ⟨seed, lift, t, ht_ne, hside, hgood, hclift,
    htarget, hcLinear, hsmall⟩
  exact ⟨seed, lift, t, ht_ne, hside, hgood, hclift, htarget, hcLinear, hsmall⟩

/-- Gauge one-sided forced cost forgets to gauge pure C-lift cost at a nonzero
scalar target. -/
theorem exists_nonzero_target_gaugePureForcedCLiftCostAtMost_of_gaugeOneSidedForcedCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) {B : ℤ}
    (h : T.GaugeOneSidedForcedCostAtMost P G B) :
    ∃ t : ℤ, t ≠ 0 ∧ T.GaugePureForcedCLiftCostAtMost G t B := by
  rcases h with ⟨_seed, lift, t, ht_ne, _hside, _hgood, _hclift,
    _htarget, hcLinear, hsmall⟩
  exact ⟨t, ht_ne, T.gaugePureForcedCLiftCostAtMost_of_witness G hcLinear hsmall⟩

/-- Gauge one-sided forced cost gives a small strict candidate in that gauge. -/
theorem hasSmallStrictCandidateWith_of_gaugeOneSidedForcedCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) {B : ℤ}
    (h : T.GaugeOneSidedForcedCostAtMost P G B) :
    T.HasSmallStrictCandidateWith G B := by
  rcases h with ⟨seed, lift, _t, _ht_ne, _hside, hgood, hclift,
    _htarget, _hcLinear, hsmall⟩
  exact ⟨lift, T.strictCandidate_of_goodSeed_and_cLift seed lift hgood.2 hclift, hsmall⟩

end ABCTriple
end ABD2
