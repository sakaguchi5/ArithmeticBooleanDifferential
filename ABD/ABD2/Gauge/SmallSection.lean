import ABD.ABD2.Gauge.CoordinateGauge
import ABD.ABD2.Fibration.FiniteSmallSection

namespace ABD2
namespace ABCTriple

/-- A gauge-small point in the C-fiber over a fixed seed. -/
def GaugeSmallFiberPoint
    (T : ABCTriple) (G : T.Gauge)
    (seed lift : T.FullTangent) (B : ℤ) : Prop :=
  lift ∈ T.FiberOver seed ∧ G.small lift B

/-- The C-fiber over a seed contains a point satisfying the gauge bound `B`. -/
def HasGaugeSmallFiberOver
    (T : ABCTriple) (G : T.Gauge) (seed : T.FullTangent) (B : ℤ) : Prop :=
  ∃ lift : T.FullTangent, T.GaugeSmallFiberPoint G seed lift B

/-- Coordinate-gauge fiber smallness is the existing coordinate-small fiber
condition. -/
theorem hasGaugeSmallFiberOver_coordinateGauge_iff_hasSmallFiberOver
    (T : ABCTriple) (seed : T.FullTangent) (B : ℤ) :
    T.HasGaugeSmallFiberOver T.coordinateGauge seed B ↔
      T.HasSmallFiberOver seed B := by
  constructor
  · intro h
    rcases h with ⟨lift, hpoint⟩
    rcases hpoint with ⟨hfiber, hsmall⟩
    exact ⟨lift, hfiber, hsmall⟩
  · intro h
    rcases h with ⟨lift, hpoint⟩
    rcases hpoint with ⟨hfiber, hsmall⟩
    exact ⟨lift, hfiber, hsmall⟩

/-- Gauge comparison transports fiber-smallness. -/
theorem hasGaugeSmallFiberOver_of_gaugeDominates
    (T : ABCTriple) {G H : T.Gauge} {seed : T.FullTangent} {B : ℤ}
    (hdom : T.GaugeDominates G H)
    (h : T.HasGaugeSmallFiberOver G seed B) :
    T.HasGaugeSmallFiberOver H seed B := by
  rcases h with ⟨lift, hpoint⟩
  rcases hpoint with ⟨hfiber, hsmall⟩
  exact ⟨lift, hfiber, hdom lift B hsmall⟩

/-- Existence of a gauge-small section over some good base point. -/
def GaugeSmallSectionExists
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile) (B : ℤ) : Prop :=
  ∃ seed : T.FullTangent,
    T.GoodBasePoint P seed ∧ T.HasGaugeSmallFiberOver G seed B

/-- Coordinate-gauge small sections are exactly the existing coordinate-small
sections. -/
theorem gaugeSmallSectionExists_coordinateGauge_iff_smallSectionExists
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) :
    T.GaugeSmallSectionExists T.coordinateGauge P B ↔
      T.SmallSectionExists P B := by
  constructor
  · intro h
    rcases h with ⟨seed, hgood, hfiber⟩
    exact ⟨seed, hgood,
      (T.hasGaugeSmallFiberOver_coordinateGauge_iff_hasSmallFiberOver seed B).1 hfiber⟩
  · intro h
    rcases h with ⟨seed, hgood, hfiber⟩
    exact ⟨seed, hgood,
      (T.hasGaugeSmallFiberOver_coordinateGauge_iff_hasSmallFiberOver seed B).2 hfiber⟩

/-- Gauge comparison transports small sections. -/
theorem gaugeSmallSectionExists_of_gaugeDominates
    (T : ABCTriple) {G H : T.Gauge} {P : T.CImageProfile} {B : ℤ}
    (hdom : T.GaugeDominates G H)
    (h : T.GaugeSmallSectionExists G P B) :
    T.GaugeSmallSectionExists H P B := by
  rcases h with ⟨seed, hgood, hfiber⟩
  exact ⟨seed, hgood, T.hasGaugeSmallFiberOver_of_gaugeDominates hdom hfiber⟩

/-- A gauge-small section gives a strict candidate satisfying the same gauge. -/
theorem hasSmallStrictCandidateWith_of_gaugeSmallSectionExists
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile) {B : ℤ}
    (h : T.GaugeSmallSectionExists G P B) :
    T.HasSmallStrictCandidateWith G B := by
  rcases h with ⟨seed, hgood, hfiber⟩
  rcases hfiber with ⟨lift, hpoint⟩
  rcases hpoint with ⟨hfiberMem, hsmall⟩
  rcases hgood with ⟨_hcompatible, hnondegenerate⟩
  have hlift : T.HasCLift seed lift :=
    (T.mem_FiberOver_iff seed lift).1 hfiberMem
  have hstrict : T.StrictCandidate lift :=
    T.strictCandidate_of_goodSeed_and_cLift seed lift hnondegenerate hlift
  exact ⟨lift, hstrict, hsmall⟩

/-- Existing coordinate-small sections give coordinate-gauge small strict
candidates. -/
theorem hasSmallStrictCandidateWith_coordinateGauge_of_smallSectionExists
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.SmallSectionExists P B) :
    T.HasSmallStrictCandidateWith T.coordinateGauge B := by
  have hgauge : T.GaugeSmallSectionExists T.coordinateGauge P B :=
    (T.gaugeSmallSectionExists_coordinateGauge_iff_smallSectionExists P B).2 h
  exact T.hasSmallStrictCandidateWith_of_gaugeSmallSectionExists
    T.coordinateGauge P hgauge

/-- A fixed seed has some finite gauge-small fiber point. -/
def HasFiniteGaugeSmallFiberOver
    (T : ABCTriple) (G : T.Gauge) (seed : T.FullTangent) : Prop :=
  ∃ B : ℤ, T.HasGaugeSmallFiberOver G seed B

/-- A profile has a finite gauge-small section if some bound works over some good
base point. -/
def HasFiniteGaugeSmallSection
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile) : Prop :=
  ∃ B : ℤ, T.GaugeSmallSectionExists G P B

@[simp]
theorem hasFiniteGaugeSmallSection_iff_exists_gaugeSmallSectionExists
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile) :
    T.HasFiniteGaugeSmallSection G P ↔
      ∃ B : ℤ, T.GaugeSmallSectionExists G P B := by
  rfl

/-- Coordinate-gauge finite small sections are exactly the Phase 5 finite small
sections. -/
theorem hasFiniteGaugeSmallSection_coordinateGauge_iff_hasFiniteSmallSection
    (T : ABCTriple) (P : T.CImageProfile) :
    T.HasFiniteGaugeSmallSection T.coordinateGauge P ↔
      T.HasFiniteSmallSection P := by
  constructor
  · intro h
    rcases h with ⟨B, hgauge⟩
    exact ⟨B, (T.gaugeSmallSectionExists_coordinateGauge_iff_smallSectionExists P B).1 hgauge⟩
  · intro h
    rcases h with ⟨B, hsection⟩
    exact ⟨B, (T.gaugeSmallSectionExists_coordinateGauge_iff_smallSectionExists P B).2 hsection⟩

/-- Gauge comparison transports finite small sections. -/
theorem hasFiniteGaugeSmallSection_of_gaugeDominates
    (T : ABCTriple) {G H : T.Gauge} {P : T.CImageProfile}
    (hdom : T.GaugeDominates G H)
    (h : T.HasFiniteGaugeSmallSection G P) :
    T.HasFiniteGaugeSmallSection H P := by
  rcases h with ⟨B, hsection⟩
  exact ⟨B, T.gaugeSmallSectionExists_of_gaugeDominates hdom hsection⟩

/-- Existence of a strict candidate satisfying some finite bound in a chosen
gauge. -/
def HasFiniteSmallStrictCandidateWith
    (T : ABCTriple) (G : T.Gauge) : Prop :=
  ∃ B : ℤ, T.HasSmallStrictCandidateWith G B

/-- A finite gauge-small section produces a finite gauge-small strict candidate. -/
theorem hasFiniteSmallStrictCandidateWith_of_hasFiniteGaugeSmallSection
    (T : ABCTriple) (G : T.Gauge) (P : T.CImageProfile)
    (h : T.HasFiniteGaugeSmallSection G P) :
    T.HasFiniteSmallStrictCandidateWith G := by
  rcases h with ⟨B, hsection⟩
  exact ⟨B, T.hasSmallStrictCandidateWith_of_gaugeSmallSectionExists G P hsection⟩

/-- Coordinate-gauge finite strict candidates are exactly the Phase 5 finite
coordinate-small strict candidates. -/
theorem hasFiniteSmallStrictCandidateWith_coordinateGauge_iff_hasFiniteSmallStrictCandidate
    (T : ABCTriple) :
    T.HasFiniteSmallStrictCandidateWith T.coordinateGauge ↔
      T.HasFiniteSmallStrictCandidate := by
  constructor
  · intro h
    rcases h with ⟨B, x, hstrict, hsmall⟩
    exact ⟨B, x, hstrict, hsmall⟩
  · intro h
    rcases h with ⟨B, x, hstrict, hsmall⟩
    exact ⟨B, x, hstrict, hsmall⟩

/-- A finite gauge-small strict candidate is, after forgetting the bound and the
gauge, an ordinary strict candidate. -/
theorem hasStrictCandidate_of_hasFiniteSmallStrictCandidateWith
    (T : ABCTriple) (G : T.Gauge)
    (h : T.HasFiniteSmallStrictCandidateWith G) :
    T.HasStrictCandidate := by
  rcases h with ⟨_B, x, hstrict, _hsmall⟩
  exact ⟨x, hstrict⟩

end ABCTriple
end ABD2
