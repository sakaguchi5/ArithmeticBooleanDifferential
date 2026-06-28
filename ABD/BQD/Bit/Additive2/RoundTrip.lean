import ABD.BQD.Bit.Additive2.Completeness

namespace ABD
namespace BQD
namespace Bit
namespace Additive2

/-- A canonical normal form represents the ordinary additive pair `(x,y)` over
its fixed output type parameter `c` when its recovered inputs are exactly `x`
and `y`.  The output is already encoded by the type `NormalForm c`. -/
def Represents {c : ℕ} (F : NormalForm c) (x y : ℕ) : Prop :=
  F.a = x ∧ F.b = y

/-- The entrance constructor represents the original ordinary additive data. -/
theorem represents_ofAddEq (x y c : ℕ) (hadd : x + y = c) :
    Represents (ofAddEq x y c hadd) x y := by
  constructor
  · exact ofAddEq_a x y c hadd
  · exact ofAddEq_b x y c hadd

/-- Any representing canonical normal form gives back ordinary addition. -/
theorem add_eq_of_represents {x y c : ℕ}
    {F : NormalForm c} (hF : Represents F x y) :
    x + y = c := by
  rcases hF with ⟨ha, hb⟩
  calc
    x + y = F.a + F.b := by
      rw [← ha, ← hb]
    _ = c := NormalForm.add_eq_c F

/-- Ordinary addition produces a canonical normal form representing the same
input pair. -/
theorem exists_normalForm_of_add_eq (x y c : ℕ)
    (hadd : x + y = c) :
    ∃ F : NormalForm c, Represents F x y := by
  exact ⟨ofAddEq x y c hadd, represents_ofAddEq x y c hadd⟩

/-- Round-trip statement: ordinary addition is equivalent to the existence of a
canonical bit-additive normal form representing the same input pair.

Unlike the fixed-width version, there is no external `c < 2^width` conjunct;
the width is canonically `bitLength c`. -/
theorem exists_normalForm_iff_add_eq (x y c : ℕ) :
    (∃ F : NormalForm c, Represents F x y) ↔ x + y = c := by
  constructor
  · rintro ⟨F, hF⟩
    exact add_eq_of_represents hF
  · intro hadd
    exact exists_normalForm_of_add_eq x y c hadd

end Additive2
end Bit
end BQD
end ABD
