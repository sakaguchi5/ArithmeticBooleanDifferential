--import Mathlib.Data.Nat.GCD.Basic
import ABD.ABD.PastenBlock.Primitive

namespace ABD

/-- The usual primitive hypothesis for an additive triple: `a` and `b` are
coprime.  Since an `ABCTriple` already carries `a + b = c`, this is enough to
recover the pairwise primitive form used by the support-block layer. -/
def ABCTriple.PrimitiveAB (T : ABCTriple) : Prop :=
  Nat.Coprime T.a T.b

/-- In an additive triple, `gcd(a,b)=1` implies `gcd(a,c)=1`. -/
theorem ABCTriple.coprimeAC_of_coprimeAB
    (T : ABCTriple) (hcop : Nat.Coprime T.a T.b) :
    Nat.Coprime T.a T.c := by
  change Nat.gcd T.a T.c = 1
  apply Nat.dvd_antisymm
  · let g := Nat.gcd T.a T.c
    have hga : g ∣ T.a := Nat.gcd_dvd_left T.a T.c
    have hgc : g ∣ T.c := Nat.gcd_dvd_right T.a T.c
    have hgab : g ∣ T.a + T.b := by
      rw [T.h_add]
      exact hgc
    have hgb : g ∣ T.b := by
      have hsub : g ∣ (T.a + T.b) - T.a := Nat.dvd_sub hgab hga
      simpa [Nat.add_sub_cancel_left] using hsub
    have hggcd : g ∣ Nat.gcd T.a T.b := Nat.dvd_gcd hga hgb
    have hgcd_one : Nat.gcd T.a T.b = 1 := hcop
    simpa [g, hgcd_one] using hggcd
  · exact Nat.one_dvd _

/-- In an additive triple, `gcd(a,b)=1` implies `gcd(b,c)=1`. -/
theorem ABCTriple.coprimeBC_of_coprimeAB
    (T : ABCTriple) (hcop : Nat.Coprime T.a T.b) :
    Nat.Coprime T.b T.c := by
  change Nat.gcd T.b T.c = 1
  apply Nat.dvd_antisymm
  · let g := Nat.gcd T.b T.c
    have hgb : g ∣ T.b := Nat.gcd_dvd_left T.b T.c
    have hgc : g ∣ T.c := Nat.gcd_dvd_right T.b T.c
    have hgab : g ∣ T.a + T.b := by
      rw [T.h_add]
      exact hgc
    have hga : g ∣ T.a := by
      have hsub : g ∣ (T.a + T.b) - T.b := Nat.dvd_sub hgab hgb
      simpa [Nat.add_sub_cancel_right] using hsub
    have hggcd : g ∣ Nat.gcd T.a T.b := Nat.dvd_gcd hga hgb
    have hgcd_one : Nat.gcd T.a T.b = 1 := hcop
    simpa [g, hgcd_one] using hggcd
  · exact Nat.one_dvd _

/-- The usual primitive hypothesis `gcd(a,b)=1` implies the pairwise primitive
form used internally by the support-block decomposition. -/
theorem ABCTriple.primitive_of_coprimeAB
    (T : ABCTriple) (hcop : Nat.Coprime T.a T.b) : T.Primitive where
  coprimeAB := hcop
  coprimeAC := T.coprimeAC_of_coprimeAB hcop
  coprimeBC := T.coprimeBC_of_coprimeAB hcop

/-- The usual primitive hypothesis implies support-level block disjointness. -/
theorem ABCTriple.supportBlocksDisjoint_of_coprimeAB
    (T : ABCTriple) (hcop : Nat.Coprime T.a T.b) :
    T.SupportBlocksDisjoint :=
  T.supportBlocksDisjoint_of_primitive (T.primitive_of_coprimeAB hcop)

/-- Under the usual primitive hypothesis, glued blocks satisfy Pasten's additive
condition exactly when they satisfy block balance. -/
theorem ABCTriple.glueBlocks_mem_pastenT_iff_blockBalance_of_coprimeAB
    (T : ABCTriple) (hcop : Nat.Coprime T.a T.b) (x : T.TangentBlocks) :
    T.glueBlocks x ∈ PastenT T ↔ T.BlockBalance x := by
  exact T.glueBlocks_mem_pastenT_iff_blockBalance
    (T.supportBlocksDisjoint_of_coprimeAB hcop) x

end ABD
