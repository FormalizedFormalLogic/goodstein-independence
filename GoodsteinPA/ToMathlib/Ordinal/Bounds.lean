/-
# Ordinal-arithmetic helper lemmas (ToMathlib candidates)

General `Ordinal` facts about `ω`-exponentiation, `+`, `max`, and `⨆`, used by the `Z_∞`
cut-elimination bounds but independent of that development.
-/
module

public import Mathlib.SetTheory.Ordinal.Principal
public import Mathlib.SetTheory.Ordinal.Veblen

@[expose] public section

namespace Ordinal

open scoped Ordinal

variable (a b c : Ordinal) (f : ℕ → Ordinal)

/-- Bound bookkeeping for a binary commuting case: a rule reassembled at `max (a+b+1) (a+c+1) + 1`
fits the target `a + (max b c + 1) + 1`. -/
lemma max_add_add_one_add_one_le : max (a + b + 1) (a + c + 1) + 1 ≤ a + (max b c + 1) + 1 := by
  refine add_le_add_left (max_le ?_ ?_) 1
  · calc a + b + 1 = a + (b + 1) := add_assoc a b 1
      _ ≤ a + (max b c + 1) := (add_le_add_iff_left a).mpr (add_le_add_left (le_max_left b c) 1)
  · calc a + c + 1 = a + (c + 1) := add_assoc a c 1
      _ ≤ a + (max b c + 1) := (add_le_add_iff_left a).mpr (add_le_add_left (le_max_right b c) 1)

/-- Bound bookkeeping for a unary commuting case (∨/∃): `a + b + 1 + 1 = a + (b + 1) + 1`. -/
lemma add_add_one_add_one_le : a + b + 1 + 1 ≤ a + (b + 1) + 1 :=
  le_of_eq (by rw [add_assoc a b 1])

/-- Bound bookkeeping for the ω-rule commuting case. -/
lemma iSup_add_add_one_add_one_le : (⨆ n, (a + f n + 1)) + 1 ≤ a + ((⨆ n, f n) + 1) + 1 := by
  refine add_le_add_left ?_ 1
  apply Ordinal.iSup_le
  intro n
  calc a + f n + 1 = a + (f n + 1) := add_assoc a (f n) 1
    _ ≤ a + ((⨆ m, f m) + 1) := (add_le_add_iff_left a).mpr (add_le_add_left (Ordinal.le_iSup f n) 1)

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

/-- `max (ω^a) (ω^b) + 1 ≤ ω^(max a b + 1)`. -/
lemma max_opow_add_one_le : max (ω ^ a) (ω ^ b) + 1 ≤ ω ^ (max a b + 1) :=
  (isPrincipal_add_omega0_opow _ (opow_lt_opow_succ_of_le_max le_rfl) (one_lt_opow_succ _)).le

/-- `max (ω^a) (ω^b) + 1 + 1 ≤ ω^(max a b + 1)`. -/
lemma max_opow_add_two_le : max (ω ^ a) (ω ^ b) + 1 + 1 ≤ ω ^ (max a b + 1) := by
  have hP := isPrincipal_add_omega0_opow (max a b + 1)
  exact (hP (hP (opow_lt_opow_succ_of_le_max le_rfl) (one_lt_opow_succ _)) (one_lt_opow_succ _)).le

/-- `ω^a + ω^b + 1 ≤ ω^(max a b + 1)`. -/
lemma opow_add_opow_add_one_le : ω ^ a + ω ^ b + 1 ≤ ω ^ (max a b + 1) := by
  have hP := isPrincipal_add_omega0_opow (max a b + 1)
  exact (hP (hP (opow_lt_opow_succ_of_le_max (le_max_left _ _))
    (opow_lt_opow_succ_of_le_max (le_max_right _ _))) (one_lt_opow_succ _)).le

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
lemma mul_add_lt {d a b x x' : Ordinal} (hab : a < b) (hx' : x' < d) : d * a + x' < d * b + x := by
  calc d * a + x' < d * a + d := (add_lt_add_iff_left _).2 hx'
    _ = d * (a + 1) := by rw [mul_add, mul_one]
    _ ≤ d * b := mul_le_mul_right (by exact_mod_cast Order.succ_le_of_lt hab) d
    _ ≤ d * b + x := le_self_add

/-- `ε₀` is closed under `ω^·`. -/
@[grind →]
lemma omega0_opow_lt_epsilon0 {a : Ordinal} (h : a < ε₀) : ω ^ a < ε₀ := by
  obtain ⟨n, hn⟩ := lt_epsilon_zero.mp h
  have hstep : ω ^ a < (fun d => ω ^ d)^[n + 1] 0 := by
    rw [Function.iterate_succ_apply']
    exact (opow_lt_opow_iff_right one_lt_omega0).mpr hn
  exact hstep.trans (iterate_omega0_opow_lt_epsilon_zero (n + 1))

end Ordinal
