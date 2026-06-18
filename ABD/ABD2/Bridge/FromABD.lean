import ABD.ABD2.Reduction.All
import ABD.PastenBlock.All

namespace ABD2

/-- Bridge marker: ABD2 is intended as the Boolean-mask-module refactor of the
current ABD/PastenBlock development.

The actual transport of concrete ABD theorems into ABD2 should be done after the
ABD2 mask layer is accepted, so this file intentionally contains only a harmless
marker proposition and imports both worlds. -/
def FromABDReady : Prop := True

theorem fromABDReady : FromABDReady := by
  trivial

end ABD2
