import ABD.ABD3.Views.ExponentSurplus

namespace ABD3

open Finset

/-- Positive part of a signed exponent surplus. -/
def PositivePart (z : ℤ) : ℤ :=
  max z 0

/-- Negative deficit of a signed exponent surplus, recorded as a nonnegative
integer-valued `ℤ`. -/
def NegativePart (z : ℤ) : ℤ :=
  max (-z) 0

namespace ABCData

/-- Total signed full-support exponent surplus. -/
def TotalFullExponentSurplus (T : ABCData) (P : PowerData) : ℤ :=
  T.supportABC.sum (fun p => T.ExponentSurplusAt P p)

/-- Total positive full-support surplus. -/
def PositiveFullSurplus (T : ABCData) (P : PowerData) : ℤ :=
  T.supportABC.sum (fun p => PositivePart (T.ExponentSurplusAt P p))

/-- Total full-support deficit.  This includes A/B-only tax and C-primes whose
valuation reward does not beat their radical tax. -/
def NegativeFullDeficit (T : ABCData) (P : PowerData) : ℤ :=
  T.supportABC.sum (fun p => NegativePart (T.ExponentSurplusAt P p))

/-- The normal-form dominance statement: positive surplus beats total deficit. -/
def PositiveSurplusDominatesDeficit (T : ABCData) (P : PowerData) : Prop :=
  T.NegativeFullDeficit P < T.PositiveFullSurplus P

/-- Every signed surplus decomposes into positive surplus minus deficit. -/
theorem int_eq_positivePart_sub_negativePart (z : ℤ) :
    z = PositivePart z - NegativePart z := by
  unfold PositivePart NegativePart
  by_cases hz : 0 ≤ z
  · have hneg : -z ≤ 0 := neg_nonpos.mpr hz
    rw [max_eq_left hz, max_eq_right hneg]
    simp
  · have hzle : z ≤ 0 := le_of_not_ge hz
    have hneg : 0 ≤ -z := neg_nonneg.mpr hzle
    rw [max_eq_right hzle, max_eq_left hneg]
    simp

/-- The full-support total surplus is positive surplus minus total deficit. -/
theorem totalFullExponentSurplus_eq_positive_sub_negative
    (T : ABCData) (P : PowerData) :
    T.TotalFullExponentSurplus P =
      T.PositiveFullSurplus P - T.NegativeFullDeficit P := by
  unfold TotalFullExponentSurplus PositiveFullSurplus NegativeFullDeficit
  calc
    T.supportABC.sum (fun p => T.ExponentSurplusAt P p)
        = T.supportABC.sum
            (fun p => PositivePart (T.ExponentSurplusAt P p) -
              NegativePart (T.ExponentSurplusAt P p)) := by
          apply Finset.sum_congr rfl
          intro p _
          exact int_eq_positivePart_sub_negativePart (T.ExponentSurplusAt P p)
    _ = T.supportABC.sum (fun p => PositivePart (T.ExponentSurplusAt P p)) -
        T.supportABC.sum (fun p => NegativePart (T.ExponentSurplusAt P p)) := by
          rw [Finset.sum_sub_distrib]

/-- Theorem C: saying that the total signed surplus is positive is exactly saying
that positive surplus dominates the total deficit.

This is the additive exponent-surplus normal form behind the informal statement
that C-side surplus has to pay for A/B tax and all C-side negative surplus. -/
theorem theoremC_totalPositive_iff_positiveDominates
    (T : ABCData) (P : PowerData) :
    0 < T.TotalFullExponentSurplus P ↔
      T.PositiveSurplusDominatesDeficit P := by
  unfold PositiveSurplusDominatesDeficit
  rw [T.totalFullExponentSurplus_eq_positive_sub_negative P]
  exact sub_pos

end ABCData
end ABD3
