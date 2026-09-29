/-
# `fastGrowingε₀` — the diagonal `f_{ε₀}`

Index domination of `fastGrowing` by the `ε₀`-diagonal `fastGrowingε₀`.
-/
module

public import GoodsteinPA.ToMathlib.FastGrowing.Norm

@[expose] public section

namespace ONote

open ONote Ordinal

/-- `fastGrowingε₀ i = f_{tower i}(i)` — the definitional unfolding, as a named lemma. -/
lemma fastGrowingε₀_eq (i : ℕ) : fastGrowingε₀ i = fastGrowing (tower i) i := rfl

end ONote
