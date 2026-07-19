/-
# Rank and order type of a well-founded relation on `ℕ`

For a well-founded relation `lt` on `ℕ`:
- `rk lt n = |n|_lt` (the `lt`-rank), via mathlib `IsWellFounded.rank`;
- `orderType lt = ‖lt‖ = sup{|n|_lt + 1 : n}` (the order type of `lt`).
-/
module

public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

namespace WellFoundedRank

variable (lt : ℕ → ℕ → Prop) [IsWellFounded ℕ lt]

/-- `|n|_lt` — the `lt`-rank, `sup{|i|_lt + 1 : i lt n}` (mathlib `IsWellFounded.rank`). -/
noncomputable def rk (n : ℕ) : Ordinal.{0} := IsWellFounded.rank lt n

lemma rk_lt_of_rel {a b : ℕ} (h : lt a b) : rk lt a < rk lt b :=
  IsWellFounded.rank_lt_of_rel h

/-- `|n|_lt ≤ γ` whenever every `lt`-predecessor has rank `< γ` (the rank recursion
`|n|_lt = sup{|m|_lt+1 : m lt n}`). -/
lemma rk_le_of_forall {γ : Ordinal.{0}} {n : ℕ} (h : ∀ m, lt m n → rk lt m < γ) :
    rk lt n ≤ γ := by
  rw [rk, IsWellFounded.rank_eq]
  apply Ordinal.iSup_le
  rintro ⟨m, hm⟩
  exact Order.succ_le_of_lt (h m hm)

/-- `‖lt‖` — the order type, `sup{|n|_lt + 1}`. -/
noncomputable def orderType : Ordinal.{0} := ⨆ n : ℕ, Order.succ (rk lt n)

/-- Every rank is `< ‖lt‖.succ`; more usefully, `|n|_lt < γ` for all `n` forces `‖lt‖ ≤ γ`. -/
lemma orderType_le_of_forall {γ : Ordinal.{0}} (h : ∀ n, rk lt n < γ) : orderType lt ≤ γ := by
  refine Ordinal.iSup_le ?_
  intro n
  exact Order.succ_le_of_lt (h n)

end WellFoundedRank
