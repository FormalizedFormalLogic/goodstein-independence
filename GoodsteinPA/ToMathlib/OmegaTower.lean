/-
# The ordinal ω-tower `omegaTower`

`omegaTower c α` iterates `ω ^ ·` on `α` `c` times (`omegaTower 0 α = α`,
`omegaTower (c+1) α = omegaTower c (ω ^ α)`), together with its `ε₀`-closure.
-/
module

public import GoodsteinPA.ToMathlib.Ordinal

@[expose] public section

namespace Ordinal

/-- Towsner **Def 19.8**: `ω`-tower over `α` of height `c` (`ω_c^α`), bottom-up:
`ω_0^α = α`, `ω_{c+1}^α = ω_c^(ω^α)`. The cut-elimination ordinal blow-up. -/
@[grind =]
noncomputable def omegaTower : ℕ → Ordinal → Ordinal
  | 0, α => α
  | c + 1, α => omegaTower c (Ordinal.omega0 ^ α)

@[simp, grind =] lemma omegaTower_zero (α : Ordinal) : omegaTower 0 α = α := rfl

@[simp, grind =] lemma omegaTower_one (α : Ordinal) : omegaTower 1 α = Ordinal.omega0 ^ α := rfl

open scoped Ordinal in
/-- The full cut-elimination ordinal `ω_c^α` stays below `ε₀` whenever `α < ε₀`. -/
lemma omegaTower_lt_epsilon0 : ∀ (c : ℕ) {α : Ordinal}, α < ε₀ → omegaTower c α < ε₀
  | 0, _, h => by simpa [omegaTower] using h
  | c + 1, _, h => by
    simpa [omegaTower] using omegaTower_lt_epsilon0 c (omega0_opow_lt_epsilon0 h)

end Ordinal
