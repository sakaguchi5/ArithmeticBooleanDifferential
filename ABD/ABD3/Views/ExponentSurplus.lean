import ABD.ABD3.Views.SupportProduct

namespace ABD3

namespace ABCData

/-- Full-support exponent surplus at a prime:
C-height reward minus full ABC radical-support tax. -/
def ExponentSurplusAt (T : ABCData) (P : PowerData) (p : ℕ) : ℤ :=
  (T.CValuationRewardAt P p : ℤ) - (T.SupportTaxAt P p : ℤ)

/-- C-side positive-surplus primes: primes of `C` whose C-height reward beats
one unit of radical tax. -/
def HasPositiveCSurplus (T : ABCData) (P : PowerData) : Prop :=
  ∃ p : ℕ, p ∈ T.supportC ∧ 0 < T.CSurplusAt P p

/-- On the C support, the full-support exponent surplus agrees with the C-side
bookkeeping surplus. -/
@[simp] theorem exponentSurplusAt_eq_cSurplusAt_of_mem_supportC
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hp : p ∈ T.supportC) :
    T.ExponentSurplusAt P p = T.CSurplusAt P p := by
  have hpABC : p ∈ T.supportABC := by
    simp [supportABC, hp]
  simp [ExponentSurplusAt, CSurplusAt, SupportTaxAt, CSupportTaxAt,
    SupportTax, hpABC, hp]

/-- On C-support primes, full surplus has the expected local form
`M * v_p(C) - N`. -/
@[simp] theorem exponentSurplusAt_of_mem_supportC
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hp : p ∈ T.supportC) :
    T.ExponentSurplusAt P p =
      (T.CValuationRewardAt P p : ℤ) - (P.N : ℤ) := by
  rw [T.exponentSurplusAt_eq_cSurplusAt_of_mem_supportC P hp]
  simp [hp]

/-- Outside the full ABC support, the radical tax vanishes in the local surplus. -/
@[simp] theorem exponentSurplusAt_of_not_mem_supportABC
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hp : p ∉ T.supportABC) :
    T.ExponentSurplusAt P p = (T.CValuationRewardAt P p : ℤ) := by
  simp [ExponentSurplusAt, hp]

/-- Theorem B: a positive C-surplus prime is exactly a C-prime whose C-height
reward is larger than the local radical tax `N`.

This is the local form of the slogan: dangerous radical-smallness must be paid
for by high C-side valuation. -/
theorem theoremB_positiveCSurplus_iff_highCReward
    (T : ABCData) (P : PowerData) :
    T.HasPositiveCSurplus P ↔
      ∃ p : ℕ, p ∈ T.supportC ∧
        (P.N : ℤ) < (T.CValuationRewardAt P p : ℤ) := by
  constructor
  · rintro ⟨p, hp, hpos⟩
    refine ⟨p, hp, ?_⟩
    rw [T.cSurplusAt_of_mem_supportC P hp] at hpos
    exact sub_pos.mp hpos
  · rintro ⟨p, hp, hlt⟩
    refine ⟨p, hp, ?_⟩
    rw [T.cSurplusAt_of_mem_supportC P hp]
    exact sub_pos.mpr hlt

end ABCData
end ABD3
