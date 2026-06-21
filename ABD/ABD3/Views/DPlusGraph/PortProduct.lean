import ABD.ABD3.Views.DPlusGraph.CPortRefinement

namespace ABD3

namespace ABCData

/-- The positive C-port mass written as an explicit product over the positive
surplus ports, rather than as a product over the full ABC support. -/
def CPortMassProductOnPorts (T : ABCData) (P : PowerData) : ℕ :=
  (T.CSurplusPorts P).prod (fun p => p ^ T.PositiveSurplusExpAt P p)

/-- Outside the positive C-port filter, a full-support prime has zero positive
surplus exponent. -/
theorem positiveSurplusExpAt_eq_zero_of_mem_supportABC_of_not_mem_cSurplusPorts
    (T : ABCData) (P : PowerData) {p : ℕ}
    (hpABC : p ∈ T.supportABC)
    (hpNot : p ∉ T.CSurplusPorts P) :
    T.PositiveSurplusExpAt P p = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  exact hpNot ((T.mem_cSurplusPorts_iff P p).mpr ⟨hpABC, hpos⟩)

/-- The D+ positive surplus product is the product over positive C-ports only. -/
theorem positiveSurplusProduct_eq_cPortMassProductOnPorts
    (T : ABCData) (P : PowerData) :
    T.PositiveSurplusProduct P = T.CPortMassProductOnPorts P := by
  unfold PositiveSurplusProduct CPortMassProductOnPorts
  symm
  refine Finset.prod_subset ?subset ?one
  · intro p hp
    exact ((T.mem_cSurplusPorts_iff P p).mp hp).1
  · intro p hpABC hpNot
    have hzero : T.PositiveSurplusExpAt P p = 0 :=
      T.positiveSurplusExpAt_eq_zero_of_mem_supportABC_of_not_mem_cSurplusPorts
        P hpABC hpNot
    simp [hzero]

/-- The graph-language C-port mass agrees with the explicit C-port product. -/
theorem cPortMassProduct_eq_cPortMassProductOnPorts
    (T : ABCData) (P : PowerData) :
    T.CPortMassProduct P = T.CPortMassProductOnPorts P := by
  rw [cPortMassProduct_eq_positiveSurplusProduct]
  exact T.positiveSurplusProduct_eq_cPortMassProductOnPorts P

end ABCData

end ABD3
