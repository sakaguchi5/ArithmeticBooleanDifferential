import ABD.ABD2.Cost.All
import ABD.ABD2.Regime.Stage0.AcceptAll
import ABD.ABD2.Regime.Stage1.ExactBound
import ABD.ABD2.Regime.Stage2.UpperBound
import ABD.ABD2.Regime.Stage3.RationalPowerSaving

namespace ABD2
namespace ABCTriple

/-- D1 accepted witness: an independent A/B preimage pair whose ambient bound is
accepted by the chosen regime.

This is deliberately a Regime-layer predicate: the cost layer constructs the
preimage witness, while this predicate records that its bound has passed the
chosen acceptance test. -/
def D1AcceptedSeparatePreimage
    (T : ABCTriple) (R : T.Regime) : Prop :=
  ∃ t B : ℤ,
    T.AcceptedBound R B ∧ T.TwoSidedSeparatePreimageCostAtMost t B

/-- D2 accepted witness: the existing one-sided forced cost in the chosen regime.

The Cost layer already normalized the one-sided forced cost as
`OneSidedForcedCostInRegime`, so the Regime layer gives it the D2 name used in
the E-roadmap. -/
abbrev D2AcceptedForcedLift
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.Regime) : Prop :=
  T.OneSidedForcedCostInRegime P G R

/-- A concrete accepted bound plus a two-sided cost witness puts the two-sided
cost in the chosen regime. -/
theorem twoSidedABCancellationCostInRegime_of_acceptedBound
    (T : ABCTriple) {R : T.Regime} {B : ℤ}
    (hB : T.AcceptedBound R B)
    (hcost : T.TwoSidedABCancellationCostAtMost B) :
    T.TwoSidedABCancellationCostInRegime R := by
  exact T.twoSidedABCancellationCostInRegime_of_bound R
    (T.accepts_of_acceptedBound hB) hcost

/-- A concrete accepted bound plus a gauge one-sided forced witness puts the
one-sided forced cost in the chosen regime. -/
theorem oneSidedForcedCostInRegime_of_acceptedBound
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) {R : T.Regime} {B : ℤ}
    (hB : T.AcceptedBound R B)
    (hcost : T.GaugeOneSidedForcedCostAtMost P G B) :
    T.OneSidedForcedCostInRegime P G R := by
  exact T.oneSidedForcedCostInRegime_of_bound P G R
    (T.accepts_of_acceptedBound hB) hcost

/-- Constructor for the D1 accepted-separate-preimage predicate. -/
theorem d1AcceptedSeparatePreimage_of_acceptedBound
    (T : ABCTriple) {R : T.Regime} {t B : ℤ}
    (hB : T.AcceptedBound R B)
    (hcost : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.D1AcceptedSeparatePreimage R := by
  exact ⟨t, B, hB, hcost⟩

/-- D1 accepted separate preimages route into the existing two-sided
in-regime cost, using the Boolean support-block glue and max-aggregate bridge. -/
theorem twoSidedABCancellationCostInRegime_of_D1AcceptedSeparatePreimage
    (T : ABCTriple) (R : T.Regime)
    (hblocks : T.SupportBlocksDecompose)
    (h : T.D1AcceptedSeparatePreimage R) :
    T.TwoSidedABCancellationCostInRegime R := by
  rcases h with ⟨t, B, hB, hcost⟩
  exact T.twoSidedABCancellationCostInRegime_of_scalarCancellationCostAtMost R
    (T.accepts_of_acceptedBound hB)
    (T.twoSidedScalarCancellationCostAtMost_of_separatePreimageCostAtMost_of_supportBlocksDecompose
      hblocks hcost)

/-- Stage 0: any two-sided cost witness is in the accept-all regime. -/
theorem twoSidedABCancellationCostInRegime_acceptAll
    (T : ABCTriple) {B : ℤ}
    (hcost : T.TwoSidedABCancellationCostAtMost B) :
    T.TwoSidedABCancellationCostInRegime T.acceptAllRegime := by
  exact T.twoSidedABCancellationCostInRegime_of_acceptedBound
    (T.acceptedBound_acceptAllRegime B) hcost

/-- Stage 0: any gauge one-sided forced witness is in the accept-all regime. -/
theorem oneSidedForcedCostInRegime_acceptAll
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) {B : ℤ}
    (hcost : T.GaugeOneSidedForcedCostAtMost P G B) :
    T.OneSidedForcedCostInRegime P G T.acceptAllRegime := by
  exact T.oneSidedForcedCostInRegime_of_acceptedBound P G
    (T.acceptedBound_acceptAllRegime B) hcost

/-- Stage 0: any independent A/B preimage witness is D1-accepted in the
accept-all regime. -/
theorem d1AcceptedSeparatePreimage_acceptAll
    (T : ABCTriple) {t B : ℤ}
    (hcost : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.D1AcceptedSeparatePreimage T.acceptAllRegime := by
  exact T.d1AcceptedSeparatePreimage_of_acceptedBound
    (T.acceptedBound_acceptAllRegime B) hcost

/-- Stage 1: a two-sided cost witness at the exact distinguished bound is in the
exact-bound regime. -/
theorem twoSidedABCancellationCostInRegime_exactBound
    (T : ABCTriple) {B₀ : ℤ}
    (hcost : T.TwoSidedABCancellationCostAtMost B₀) :
    T.TwoSidedABCancellationCostInRegime (T.exactBoundRegime B₀) := by
  exact T.twoSidedABCancellationCostInRegime_of_acceptedBound
    (T.acceptedBound_of_accepts (T.exactBoundRegime_accepts_self B₀)) hcost

/-- Stage 1: a gauge one-sided forced witness at the exact distinguished bound
is in the exact-bound regime. -/
theorem oneSidedForcedCostInRegime_exactBound
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) {B₀ : ℤ}
    (hcost : T.GaugeOneSidedForcedCostAtMost P G B₀) :
    T.OneSidedForcedCostInRegime P G (T.exactBoundRegime B₀) := by
  exact T.oneSidedForcedCostInRegime_of_acceptedBound P G
    (T.acceptedBound_of_accepts (T.exactBoundRegime_accepts_self B₀)) hcost

/-- Stage 1: an independent A/B preimage witness at the exact distinguished
bound is D1-accepted in the exact-bound regime. -/
theorem d1AcceptedSeparatePreimage_exactBound
    (T : ABCTriple) {t B₀ : ℤ}
    (hcost : T.TwoSidedSeparatePreimageCostAtMost t B₀) :
    T.D1AcceptedSeparatePreimage (T.exactBoundRegime B₀) := by
  exact T.d1AcceptedSeparatePreimage_of_acceptedBound
    (T.acceptedBound_of_accepts (T.exactBoundRegime_accepts_self B₀)) hcost

/-- Stage 2: a two-sided cost witness at `B` is accepted by an upper-bound
regime with ceiling `B₀` when `B ≤ B₀`. -/
theorem twoSidedABCancellationCostInRegime_upperBound
    (T : ABCTriple) {B B₀ : ℤ}
    (hB : B ≤ B₀)
    (hcost : T.TwoSidedABCancellationCostAtMost B) :
    T.TwoSidedABCancellationCostInRegime (T.upperBoundRegime B₀) := by
  exact T.twoSidedABCancellationCostInRegime_of_acceptedBound
    (T.acceptedBound_of_accepts (T.upperBoundRegime_accepts_of_le hB)) hcost

/-- Stage 2: a gauge one-sided forced witness at `B` is accepted by an
upper-bound regime with ceiling `B₀` when `B ≤ B₀`. -/
theorem oneSidedForcedCostInRegime_upperBound
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) {B B₀ : ℤ}
    (hB : B ≤ B₀)
    (hcost : T.GaugeOneSidedForcedCostAtMost P G B) :
    T.OneSidedForcedCostInRegime P G (T.upperBoundRegime B₀) := by
  exact T.oneSidedForcedCostInRegime_of_acceptedBound P G
    (T.acceptedBound_of_accepts (T.upperBoundRegime_accepts_of_le hB)) hcost

/-- Stage 2: an independent A/B preimage witness at `B` is D1-accepted by an
upper-bound regime with ceiling `B₀` when `B ≤ B₀`. -/
theorem d1AcceptedSeparatePreimage_upperBound
    (T : ABCTriple) {t B B₀ : ℤ}
    (hB : B ≤ B₀)
    (hcost : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.D1AcceptedSeparatePreimage (T.upperBoundRegime B₀) := by
  exact T.d1AcceptedSeparatePreimage_of_acceptedBound
    (T.acceptedBound_of_accepts (T.upperBoundRegime_accepts_of_le hB)) hcost

/-- Stage 3: a two-sided cost witness at a rational power-saving bound is in the
corresponding rational power-saving regime. -/
theorem twoSidedABCancellationCostInRegime_rationalPowerSaving
    (T : ABCTriple) (data : RationalPowerSavingData) {B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.TwoSidedABCancellationCostAtMost B) :
    T.TwoSidedABCancellationCostInRegime (T.rationalPowerSavingRegime data) := by
  exact T.twoSidedABCancellationCostInRegime_of_acceptedBound
    (T.acceptedBound_of_accepts
      (T.rationalPowerSavingRegime_accepts_of_pow_lt data hBnonneg hpow))
    hcost

/-- Stage 3: a gauge one-sided forced witness at a rational power-saving bound
is in the corresponding rational power-saving regime. -/
theorem oneSidedForcedCostInRegime_rationalPowerSaving
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (data : RationalPowerSavingData) {B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.GaugeOneSidedForcedCostAtMost P G B) :
    T.OneSidedForcedCostInRegime P G (T.rationalPowerSavingRegime data) := by
  exact T.oneSidedForcedCostInRegime_of_acceptedBound P G
    (T.acceptedBound_of_accepts
      (T.rationalPowerSavingRegime_accepts_of_pow_lt data hBnonneg hpow))
    hcost

/-- Stage 3: an independent A/B preimage witness at a rational power-saving bound
is D1-accepted in the corresponding rational power-saving regime. -/
theorem d1AcceptedSeparatePreimage_rationalPowerSaving
    (T : ABCTriple) (data : RationalPowerSavingData) {t B : ℤ}
    (hBnonneg : 0 ≤ B)
    (hpow : B ^ data.N < ((T.c : ℤ) ^ data.M))
    (hcost : T.TwoSidedSeparatePreimageCostAtMost t B) :
    T.D1AcceptedSeparatePreimage (T.rationalPowerSavingRegime data) := by
  exact T.d1AcceptedSeparatePreimage_of_acceptedBound
    (T.acceptedBound_of_accepts
      (T.rationalPowerSavingRegime_accepts_of_pow_lt data hBnonneg hpow))
    hcost

end ABCTriple
end ABD2
