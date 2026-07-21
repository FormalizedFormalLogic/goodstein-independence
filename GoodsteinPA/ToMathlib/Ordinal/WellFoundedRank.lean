/-
# Rank and order type of a well-founded relation

For a well-founded relation `lt` on a type `α`:
- `rk lt a = |a|_lt` (the `lt`-rank), via mathlib `IsWellFounded.rank`;
- `orderType lt = ‖lt‖ = sup{|a|_lt + 1 : a}` (the order type of `lt`).
-/
module

public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

namespace WellFoundedRank

variable {α : Type*} (lt : α → α → Prop) [IsWellFounded α lt]

/-- `|a|_lt` — the `lt`-rank, `sup{|b|_lt + 1 : b lt a}` (mathlib `IsWellFounded.rank`). -/
noncomputable def rk (a : α) : Ordinal := IsWellFounded.rank lt a

lemma rk_lt_of_rel {a b : α} (h : lt a b) : rk lt a < rk lt b :=
  IsWellFounded.rank_lt_of_rel h

/-- `|a|_lt ≤ γ` whenever every `lt`-predecessor has rank `< γ` (the rank recursion
`|a|_lt = sup{|b|_lt+1 : b lt a}`). -/
lemma rk_le_of_forall {γ : Ordinal} {a : α} (h : ∀ b, lt b a → rk lt b < γ) :
    rk lt a ≤ γ := by
  rw [rk, IsWellFounded.rank_eq]
  apply Ordinal.iSup_le
  intro ⟨b, hb⟩
  exact Order.succ_le_of_lt (h b hb)

/-- `‖lt‖` — the order type, `sup{|a|_lt + 1}`. -/
noncomputable def orderType : Ordinal := ⨆ a : α, Order.succ (rk lt a)

/-- Every rank is `< ‖lt‖.succ`; more usefully, `|a|_lt < γ` for all `a` forces `‖lt‖ ≤ γ`. -/
lemma orderType_le_of_forall {γ : Ordinal} (h : ∀ a, rk lt a < γ) : orderType lt ≤ γ :=
  Ordinal.iSup_le fun a => Order.succ_le_of_lt (h a)

end WellFoundedRank
