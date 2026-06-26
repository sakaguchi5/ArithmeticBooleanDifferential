import ABD.BQD.Bit.Additive.Completeness

namespace ABD
namespace BQD
namespace Bit
namespace Additive

/-- A normal form represents the ordinary additive triple `(x,y,c)` when its
recovered inputs and output are exactly those three naturals. -/
def Represents {width : ℕ} (F : NormalForm width) (x y c : ℕ) : Prop :=
  F.a = x ∧ F.b = y ∧ F.c = c

/-- The entrance constructor represents the original ordinary additive triple. -/
theorem represents_ofAddEq (width x y c : ℕ)
    (hadd : x + y = c) (hc : c < 2 ^ width) :
    Represents (ofAddEq width x y c hadd hc) x y c := by
  constructor
  · exact ofAddEq_a width x y c hadd hc
  constructor
  · exact ofAddEq_b width x y c hadd hc
  · exact ofAddEq_c width x y c hadd hc

/-- Any representing normal form gives back ordinary addition and the width
bound on the represented output. -/
theorem add_eq_and_c_lt_of_represents {width x y c : ℕ}
    {F : NormalForm width} (hF : Represents F x y c) :
    x + y = c ∧ c < 2 ^ width := by
  rcases hF with ⟨ha, hb, hcF⟩
  constructor
  · calc
      x + y = F.a + F.b := by
        rw [← ha, ← hb]
      _ = F.c := NormalForm.add_eq_c F
      _ = c := hcF
  · rw [← hcF]
    exact F.hC_lt

/-- Ordinary addition with a common-width output bound produces a representing
normal form. -/
theorem exists_normalForm_of_add_eq_and_c_lt (width x y c : ℕ)
    (hadd : x + y = c) (hc : c < 2 ^ width) :
    ∃ F : NormalForm width, Represents F x y c := by
  exact ⟨ofAddEq width x y c hadd hc, represents_ofAddEq width x y c hadd hc⟩

/-- Round-trip statement: ordinary bounded addition is equivalent to the
existence of a bit-additive normal form representing the same triple.

This is intentionally an existence statement, not a uniqueness statement for
boards or normal forms. -/
theorem exists_normalForm_iff_add_eq_and_c_lt (width x y c : ℕ) :
    (∃ F : NormalForm width, Represents F x y c) ↔
      x + y = c ∧ c < 2 ^ width := by
  constructor
  · rintro ⟨F, hF⟩
    exact add_eq_and_c_lt_of_represents hF
  · rintro ⟨hadd, hc⟩
    exact exists_normalForm_of_add_eq_and_c_lt width x y c hadd hc

end Additive
end Bit
end BQD
end ABD
