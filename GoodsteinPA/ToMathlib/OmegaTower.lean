/-
# The ordinal ω-tower `omegaTower`

`omegaTower c a` iterates `ω ^ ·` on `a` `c` times (`omegaTower 0 a = a`,
`omegaTower (c+1) a = omegaTower c (ω ^ a)`), together with its `ε₀`-closure.
-/
module

public import GoodsteinPA.ToMathlib.Ordinal.Bounds

@[expose] public section

namespace Ordinal

open scoped Ordinal

/-- Towsner **Def 19.8**: `ω`-tower over `a` of height `c` (`ω_c^a`), bottom-up:
`ω_0^a = a`, `ω_{c+1}^a = ω_c^(ω^a)`. The cut-elimination ordinal blow-up. -/
@[grind =]
noncomputable def omegaTower : ℕ → Ordinal → Ordinal
  | 0, a => a
  | c + 1, a => omegaTower c (ω ^ a)

variable {a : Ordinal}

@[simp, grind =] lemma omegaTower_zero : omegaTower 0 a = a := rfl

@[simp, grind =] lemma omegaTower_one : omegaTower 1 a = ω ^ a := rfl

/-- The full cut-elimination ordinal `ω_c^a` stays below `ε₀` whenever `a < ε₀`. -/
lemma omegaTower_lt_epsilon0 (c : ℕ) (h : a < ε₀) : omegaTower c a < ε₀ := by
  induction c generalizing a with
  | zero => simpa [omegaTower] using h
  | succ c ih => simpa [omegaTower] using ih (omega0_opow_lt_epsilon0 h)

end Ordinal
