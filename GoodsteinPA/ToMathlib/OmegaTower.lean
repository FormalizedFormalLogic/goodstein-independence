/-
# The ordinal ω-tower `omegaTower`

`omegaTower c α` iterates `ω ^ ·` on `α` `c` times (`omegaTower 0 α = α`,
`omegaTower (c+1) α = omegaTower c (ω ^ α)`), together with its `ε₀`-closure.
-/
module

public import GoodsteinPA.ToMathlib.Ordinal

@[expose] public section

namespace Ordinal

open scoped Ordinal

/-- Towsner **Def 19.8**: `ω`-tower over `α` of height `c` (`ω_c^α`), bottom-up:
`ω_0^α = α`, `ω_{c+1}^α = ω_c^(ω^α)`. The cut-elimination ordinal blow-up. -/
@[grind =]
noncomputable def omegaTower : ℕ → Ordinal → Ordinal
  | 0, α => α
  | c + 1, α => omegaTower c (ω ^ α)

variable {α : Ordinal}

@[simp, grind =] lemma omegaTower_zero : omegaTower 0 α = α := rfl

@[simp, grind =] lemma omegaTower_one : omegaTower 1 α = ω ^ α := rfl

/-- The full cut-elimination ordinal `ω_c^α` stays below `ε₀` whenever `α < ε₀`. -/
lemma omegaTower_lt_epsilon0 (c : ℕ) (h : α < ε₀) : omegaTower c α < ε₀ := by
  induction c generalizing α with
  | zero => simpa [omegaTower] using h
  | succ c ih => simpa [omegaTower] using ih (omega0_opow_lt_epsilon0 h)

end Ordinal
