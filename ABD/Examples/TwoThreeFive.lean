import ABD.Differential.All

namespace ABD.Examples

/-- The toy support `{2, 3, 5}` for the equation `2 + 3 = 5`. -/
def S235 : Finset ℕ :=
  {2, 3, 5}

/-- The zero tangent vector on `{2, 3, 5}`. -/
def zeroTangent235 : ABD.Tangent S235 :=
  ABD.zeroTangent S235

example : ABD.AdditiveOn S235 zeroTangent235 2 3 5 := by
  simp [zeroTangent235]

end ABD.Examples
