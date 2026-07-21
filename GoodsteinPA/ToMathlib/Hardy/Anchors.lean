/-
# `ONote` Hardy / fast-growing hierarchy — anti-vacuity anchors (`native_decide`)

Standalone `native_decide` witnesses, off any headline axiom path, that a wrong definition
of `hardy`, `hstep`, `fastGrowing`, `fastGrowingε₀`, or `tower` would fail to satisfy.
Kept apart from the (Mathlib-bound) bodies in `FastGrowing/Epsilon0.lean`, `Hardy/Structure.lean`,
and `Hardy/Comparison.lean` so that those files stay free of `meta` imports.
-/
module

public import GoodsteinPA.ToMathlib.Hardy.Comparison
public meta import GoodsteinPA.ToMathlib.Hardy.Structure  -- shake: keep

@[expose] public section

namespace ONote

open ONote Ordinal

/-! ### From `FastGrowing/Epsilon0.lean` -/

example : fastGrowingε₀ 0 = 1 := by native_decide
example : fastGrowingε₀ 1 = 2 := by native_decide
example : fastGrowingε₀ 2 = 2048 := by native_decide
-- the tower really is `ω^ω` at level 3 (a genuine limit-of-limits index)
example : tower 3 = oadd (oadd 1 1 0) 1 0 := by native_decide

/-! ### From `Hardy/Structure.lean`

Standalone witnesses, off any headline axiom path, that a *wrong* definition of
`hardy` would fail to satisfy. They pin both the successor branch (`H_k(n) = n + k`)
and the limit branch: mathlib's fundamental sequence for `ω` is `ω[n] = n + 1`, so
`H_ω(n) = H_{n+1}(n) = n + (n+1) = 2n + 1`. -/

example : hardy 0 5 = 5 := by native_decide
example : hardy 1 5 = 6 := by native_decide
example : hardy 2 5 = 7 := by native_decide
example : hardy 3 5 = 8 := by native_decide
example : hardy 4 5 = 9 := by native_decide
-- limit branch: `H_ω(n) = 2n + 1` (`ω = oadd 1 1 0`, `ω[n] = n + 1`)
example : hardy (oadd 1 1 0) 2 = 5 := by native_decide
example : hardy (oadd 1 1 0) 4 = 9 := by native_decide
example : hardy (oadd 1 1 0) 6 = 13 := by native_decide
-- the new closed forms / lower bound, witnessed concretely (a wrong proof would mis-evaluate):
example : hardy (ofNat 4) 5 = 5 + 4 := by native_decide       -- hardy_ofNat
example : hardy (oadd 1 1 0) 6 = 2 * 6 + 1 := by native_decide -- hardy_omega
example : 2 * 2 ≤ hardy (oadd (oadd 0 2 0) 1 0) 2 := by native_decide -- two_mul_le_hardy_pow at ω²: 4 ≤ 23
-- `hstep`: successor drops one level; `ω` at budget `3` descends to `ω[3]=4` then to `3`.
example : hstep 5 0 = 4 := by native_decide
example : hstep (oadd 1 1 0) 3 = 3 := by native_decide
-- the step invariant in action: `H_ω(3) = H_{hstep ω 3}(4) = H_3(4)`
example : hardy (oadd 1 1 0) 3 = hardy (hstep (oadd 1 1 0) 3) 4 := by native_decide

/-! ### From `Hardy/Comparison.lean` -/

-- anti-vacuity: B4 at `ω^2` — `H_{ω^2}(2) + 1 = 23 + 1 = 24 = f_2(3)`
example : hardy (oadd (ofNat 2) 1 0) 2 + 1 = fastGrowing (ofNat 2) 3 := by native_decide
-- anti-vacuity: B4 at `ω^ω` — `H_{ω^ω}(1) + 1 = 7 + 1 = 8 = f_2(2)`
example : hardy (oadd (oadd 1 1 0) 1 0) 1 + 1 = fastGrowing (ofNat 2) 2 := by native_decide
-- Faithfulness anchors — the exact `+1` shift and the falsity of the bare equality are kernel-checked.
example : hardy (oadd 0 1 0) 3 + 1 = fastGrowing 0 (3 + 1) := by native_decide
example : hardy (oadd 1 1 0) 3 + 1 = fastGrowing 1 (3 + 1) := by native_decide
example : hardy (oadd 2 1 0) 2 + 1 = fastGrowing 2 (2 + 1) := by native_decide
-- and the EQUALITY `H_{ω^α} = f_α` is FALSE (off by ≥1), so no lap re-attempts it:
example : hardy (oadd 1 1 0) 3 ≠ fastGrowing 1 3 := by native_decide

end ONote
