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

/-- `|a|_lt ≤ b` whenever every `lt`-predecessor has rank `< b` (the rank recursion `|a|_lt = sup{|c|_lt+1 : c lt a}`). -/
lemma rk_le_of_forall {b : Ordinal} {a : α} (h : ∀ c, lt c a → rk lt c < b) : rk lt a ≤ b := by
  rw [rk, IsWellFounded.rank_eq]
  apply Ordinal.iSup_le
  intro ⟨c, hc⟩
  exact Order.succ_le_of_lt (h c hc)

/-- `‖lt‖` — the order type, `sup{|a|_lt + 1}`. -/
noncomputable def orderType : Ordinal := ⨆ a : α, Order.succ (rk lt a)

/-- Every rank is `< ‖lt‖.succ`; more usefully, `|a|_lt < b` for all `a` forces `‖lt‖ ≤ b`. -/
lemma orderType_le_of_forall {b : Ordinal} (h : ∀ a, rk lt a < b) : orderType lt ≤ b :=
  Ordinal.iSup_le fun a => Order.succ_le_of_lt (h a)

end WellFoundedRank
