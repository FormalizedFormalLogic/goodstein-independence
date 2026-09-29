/-
# Ordinal-arithmetic helper lemmas (ToMathlib candidates)

General `Ordinal` facts about `ω`-exponentiation, `+`, `max`, and `⨆`, used by the `Z_∞`
cut-elimination bounds but independent of that development.

Most of this file now lives in `AlphaCentauri.ToMathlib.Ordinal.Bounds` (including the `ω`-tower
`Ordinal.omegaTower`), which is re-exported here; only the lemmas AlphaCentauri does not carry
survive below.
-/
module

public import AlphaCentauri.ToMathlib.Ordinal.Bounds

@[expose] public section

namespace Ordinal

open scoped Ordinal

variable (a : Ordinal) (f : ℕ → Ordinal)

/-- `1 < ω^(a+1)` for any ordinal `a`. -/
lemma one_lt_opow_succ : 1 < ω ^ (a + 1) := by
  calc 1 < ω := one_lt_omega0
    _ = ω ^ (1 : Ordinal) := (opow_one _).symm
    _ ≤ ω ^ (a + 1) := opow_le_opow_right omega0_pos (CanonicallyOrderedAdd.le_add_self 1 a)

/-- Any `x ≤ max (ω^a) (ω^b)` is bounded by `ω^(max a b + 1)`. -/
lemma opow_lt_opow_succ_of_le_max {a b x : Ordinal} (hx : x ≤ max (ω ^ a) (ω ^ b)) : x < ω ^ (max a b + 1) :=
  hx.trans_lt (max_lt
    ((opow_lt_opow_iff_right one_lt_omega0).mpr
      ((le_max_left a b).trans_lt (lt_add_of_pos_right _ one_pos)))
    ((opow_lt_opow_iff_right one_lt_omega0).mpr
      ((le_max_right a b).trans_lt (lt_add_of_pos_right _ one_pos))))

/-- `ω^a + 1 ≤ ω^(a+1)`. -/
lemma opow_add_one_le' : ω ^ a + 1 ≤ ω ^ (a + 1) := by
  have hP := isPrincipal_add_omega0_opow (a + 1)
  exact (hP ((opow_lt_opow_iff_right one_lt_omega0).mpr
    (lt_add_of_pos_right _ one_pos)) (one_lt_opow_succ _)).le

/-- `(⨆ n, ω^(f n)) + 1 ≤ ω^((⨆ n, f n) + 1)`. -/
lemma sup_opow_add_one_le : (⨆ n, ω ^ (f n)) + 1 ≤ ω ^ ((⨆ n, f n) + 1) := by
  have hsup : (⨆ n, ω ^ (f n)) ≤ ω ^ (⨆ n, f n) :=
    Ordinal.iSup_le fun n => opow_le_opow_right omega0_pos (Ordinal.le_iSup f n)
  have hlt : ω ^ (⨆ n, f n) < ω ^ ((⨆ n, f n) + 1) :=
    (opow_lt_opow_iff_right one_lt_omega0).mpr (lt_add_of_pos_right _ one_pos)
  exact (isPrincipal_add_omega0_opow _ (hsup.trans_lt hlt) (one_lt_opow_succ _)).le

/-- **Cross-block descent:** if `a < b` and `x' < d`, then `d*a + x' < d*b + x` for any `x`. The
lower block sits entirely below `d*(a+1) ≤ d*b`. -/
@[grind .]
lemma mul_add_lt {d a b x x' : Ordinal} (hab : a < b) (hx' : x' < d) : d * a + x' < d * b + x := by
  calc d * a + x' < d * a + d := (add_lt_add_iff_left _).2 hx'
    _ = d * (a + 1) := by rw [mul_add, mul_one]
    _ ≤ d * b := mul_le_mul_right (by exact_mod_cast Order.succ_le_of_lt hab) d
    _ ≤ d * b + x := le_self_add

end Ordinal
