import ABD.ABD.Core.Valuation

namespace ABD

/-- A positive additive triple `a + b = c`.

This is the Core-level carrier for later ABC/Pasten-style statements.  It does
not mention tangent vectors, formal derivatives, smallness, or nondegeneracy;
those belong to higher layers. -/
structure ABCTriple where
  a : ℕ
  b : ℕ
  c : ℕ
  ha_pos : 0 < a
  hb_pos : 0 < b
  hc_pos : 0 < c
  h_add : a + b = c

end ABD
