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

/-- Bound bookkeeping for a binary commuting case: a rule reassembled at `max (α+a+1) (α+b+1) + 1`
fits the target `α + (max a b + 1) + 1`. -/
lemma max_add_add_one_add_one_le (α a b : Ordinal) :
    max (α + a + 1) (α + b + 1) + 1 ≤ α + (max a b + 1) + 1 := by
  refine add_le_add_left (max_le ?_ ?_) 1
  · calc α + a + 1 = α + (a + 1) := add_assoc α a 1
      _ ≤ α + (max a b + 1) := (add_le_add_iff_left α).mpr (add_le_add_left (le_max_left a b) 1)
  · calc α + b + 1 = α + (b + 1) := add_assoc α b 1
      _ ≤ α + (max a b + 1) := (add_le_add_iff_left α).mpr (add_le_add_left (le_max_right a b) 1)

/-- Bound bookkeeping for a unary commuting case (∨/∃): `α + a + 1 + 1 = α + (a + 1) + 1`. -/
lemma add_add_one_add_one_le (α a : Ordinal) : α + a + 1 + 1 ≤ α + (a + 1) + 1 :=
  le_of_eq (by rw [add_assoc α a 1])

/-- Bound bookkeeping for the ω-rule commuting case. -/
lemma iSup_add_add_one_add_one_le (α : Ordinal) (f : ℕ → Ordinal) :
    (⨆ n, (α + f n + 1)) + 1 ≤ α + ((⨆ n, f n) + 1) + 1 := by
  refine add_le_add_left ?_ 1
  apply Ordinal.iSup_le
  intro n
  calc α + f n + 1 = α + (f n + 1) := add_assoc α (f n) 1
    _ ≤ α + ((⨆ m, f m) + 1) := (add_le_add_iff_left α).mpr (add_le_add_left (Ordinal.le_iSup f n) 1)

/-- `1 < ω^(c+1)` for any ordinal `c`. -/
lemma one_lt_opow_succ (c : Ordinal) : (1 : Ordinal) < ω ^ (c + 1) := by
  calc (1 : Ordinal) < ω := one_lt_omega0
    _ = ω ^ (1 : Ordinal) := (opow_one _).symm
    _ ≤ ω ^ (c + 1) := opow_le_opow_right omega0_pos (CanonicallyOrderedAdd.le_add_self 1 c)

/-- Any `x ≤ max (ω^a) (ω^b)` is bounded by `ω^(max a b + 1)`. -/
lemma opow_lt_opow_succ_of_le_max {a b x : Ordinal}
    (hx : x ≤ max (ω ^ a) (ω ^ b)) : x < ω ^ (max a b + 1) := by
  refine lt_of_le_of_lt hx (max_lt ?_ ?_)
  · exact (opow_lt_opow_iff_right one_lt_omega0).mpr
      (lt_of_le_of_lt (le_max_left a b) (lt_add_of_pos_right _ one_pos))
  · exact (opow_lt_opow_iff_right one_lt_omega0).mpr
      (lt_of_le_of_lt (le_max_right a b) (lt_add_of_pos_right _ one_pos))

/-- `max (ω^a) (ω^b) + 1 ≤ ω^(max a b + 1)`. -/
lemma max_opow_add_one_le (a b : Ordinal) :
    max (ω ^ a) (ω ^ b) + 1 ≤ ω ^ (max a b + 1) :=
  le_of_lt (isPrincipal_add_omega0_opow _ (opow_lt_opow_succ_of_le_max le_rfl) (one_lt_opow_succ _))

/-- `max (ω^a) (ω^b) + 1 + 1 ≤ ω^(max a b + 1)`. -/
lemma max_opow_add_two_le (a b : Ordinal) :
    max (ω ^ a) (ω ^ b) + 1 + 1 ≤ ω ^ (max a b + 1) := by
  have hP := isPrincipal_add_omega0_opow (max a b + 1)
  exact le_of_lt (hP (hP (opow_lt_opow_succ_of_le_max le_rfl) (one_lt_opow_succ _))
    (one_lt_opow_succ _))

/-- `ω^a + ω^b + 1 ≤ ω^(max a b + 1)`. -/
lemma opow_add_opow_add_one_le (a b : Ordinal) :
    ω ^ a + ω ^ b + 1 ≤ ω ^ (max a b + 1) := by
  have hP := isPrincipal_add_omega0_opow (max a b + 1)
  exact le_of_lt (hP (hP (opow_lt_opow_succ_of_le_max (le_max_left _ _))
    (opow_lt_opow_succ_of_le_max (le_max_right _ _))) (one_lt_opow_succ _))

/-- `ω^a + 1 ≤ ω^(a+1)`. -/
lemma opow_add_one_le' (a : Ordinal) : ω ^ a + 1 ≤ ω ^ (a + 1) := by
  have hP := isPrincipal_add_omega0_opow (a + 1)
  exact le_of_lt (hP ((opow_lt_opow_iff_right one_lt_omega0).mpr
    (lt_add_of_pos_right _ one_pos)) (one_lt_opow_succ _))

/-- `(⨆ n, ω^(f n)) + 1 ≤ ω^((⨆ n, f n) + 1)`. -/
lemma sup_opow_add_one_le (f : ℕ → Ordinal) :
    (⨆ n, ω ^ (f n)) + 1 ≤ ω ^ ((⨆ n, f n) + 1) := by
  have hsup : (⨆ n, ω ^ (f n)) ≤ ω ^ (⨆ n, f n) :=
    Ordinal.iSup_le fun n => opow_le_opow_right omega0_pos (Ordinal.le_iSup f n)
  have hlt : ω ^ (⨆ n, f n) < ω ^ ((⨆ n, f n) + 1) :=
    (opow_lt_opow_iff_right one_lt_omega0).mpr (lt_add_of_pos_right _ one_pos)
  exact le_of_lt (isPrincipal_add_omega0_opow _ (lt_of_le_of_lt hsup hlt) (one_lt_opow_succ _))

/-- `ε₀` is closed under `ω^·`. -/
@[grind →]
lemma omega0_opow_lt_epsilon0 {a : Ordinal} (h : a < ε₀) : ω ^ a < ε₀ := by
  obtain ⟨n, hn⟩ := lt_epsilon_zero.mp h
  have hstep : ω ^ a < (fun b => ω ^ b)^[n + 1] 0 := by
    rw [Function.iterate_succ_apply']
    exact (opow_lt_opow_iff_right one_lt_omega0).mpr hn
  exact hstep.trans (iterate_omega0_opow_lt_epsilon_zero (n + 1))

end Ordinal
