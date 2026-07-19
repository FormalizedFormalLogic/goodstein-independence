/-
# `Goodstein.Dom` — anti-vacuity anchors (`native_decide`)

Standalone `native_decide` witnesses, off any headline axiom path, that a wrong definition of
`goodsteinSeq`, `goodsteinLength`, `toONote`, `seqONote`, `hstep`, `bump`, or `ppCount` would fail
to satisfy. Kept apart from the (Mathlib-bound) bodies in `Sequence.lean`, `Growth.lean`, and
`Diagonal.lean` so that those files stay free of `meta` imports.
-/
module

public import GoodsteinPA.ToMathlib.Goodstein.Domination
public meta import Mathlib.SetTheory.Ordinal.Notation  -- shake: keep
public meta import GoodsteinPA.ToMathlib.Goodstein.Defs  -- shake: keep
public meta import GoodsteinPA.ToMathlib.Hardy  -- shake: keep
public meta import GoodsteinPA.ToMathlib.Goodstein.Domination.Sequence  -- shake: keep
public meta import GoodsteinPA.ToMathlib.Goodstein.Domination.Growth  -- shake: keep
public meta import GoodsteinPA.ToMathlib.Goodstein.Domination.Diagonal  -- shake: keep

@[expose] public section

namespace Goodstein.Dom

open ONote Ordinal

/-! ### From `Domination/Sequence.lean`

Small computed values, off any headline axiom path. A wrong definition of `goodsteinSeq` could
not satisfy these. -/

example : goodsteinLength 0 = 0 := by native_decide
example : goodsteinLength 2 = 3 := by native_decide
example : goodsteinLength 3 = 5 := by native_decide

/-! ### From `Domination/Growth.lean`

The notations are computable; small values pin them (a wrong recursion would fail). -/

example : toONote 2 1 = oadd 0 1 0 := by native_decide          -- `1 = ω^0`
example : toONote 2 2 = oadd (oadd 0 1 0) 1 0 := by native_decide -- `2 = 2^1 ↦ ω^1 = ω`
example : toONote 2 4 = oadd (oadd (oadd 0 1 0) 1 0) 1 0 := by native_decide -- `4 = 2^2 ↦ ω^ω`
example : toONote 3 5 = oadd (oadd 0 1 0) 1 (oadd 0 2 0) := by native_decide  -- `5 = 1·3^1 + 2`
-- the descent: `goodsteinSeq 3` starts `3 ↦ 3 ↦ 3 ↦ 2 ↦ …`, notations strictly drop
example : seqONote 3 0 = oadd (oadd 0 1 0) 1 (oadd 0 1 0) := by native_decide -- `G₀=3` in base 2 ↦ `ω+1`
-- the Cichoń step `hstep_toONote` (now FULLY PROVED) holds; here anchored on computable cases:
example : hstep (toONote 2 3) 2 = toONote 3 (bump 2 3 - 1) := by native_decide
example : hstep (toONote 3 5) 3 = toONote 4 (bump 3 5 - 1) := by native_decide
example : hstep (seqONote 3 0) 2 = seqONote 3 1 := by native_decide
-- C3, witnessed on a computable case: `goodsteinLength 3 = H_{seqONote 3 0}(2) − 2 = 7 − 2 = 5`
example : hardy (seqONote 3 0) 2 = goodsteinLength 3 + 2 := by native_decide

/-! ### From `Domination/Diagonal.lean` (off any headline axiom path) -/

example : hardy (oadd 1 2 (oadd 0 3 0)) 4 = hardy (oadd 1 2 0) (hardy (oadd 0 3 0) 4) := by
  native_decide
example : hardy (oadd 1 3 0) 3 = (hardy (oadd 1 1 0))^[3] 3 := by native_decide
example : fastGrowing 2 3 ≤ hardy (oadd 2 1 0) 3 := by native_decide

-- The domination inequality `fastGrowing o m ≤ goodsteinLength m + 2` holds concretely in the
-- computable regime (small `o`, where it already kicks in at small `m`). A *backwards* or
-- vacuous headline would fail these. (For `o ≥ 2` the inequality is asymptotic — it first holds
-- at `m = 4`, where `goodsteinLength` is already astronomically large and beyond `native_decide`.)
-- The growth engine, witnessed: one bump strictly grows a value above its base
-- (`bump_gt`: `4 + 1 ≤ bump 2 4 = 27`), and the term stays `≥ m` (`goodsteinSeq_ge_init`:
-- `G(4,2) = 41 ≥ 4`). A vacuous/backwards recursion would fail these.
example : 4 + 1 ≤ bump 2 4 := by native_decide
example : 4 ≤ goodsteinSeq 4 2 := by native_decide
-- `log_bump`: the leading exponent bumps itself. `bump 2 5 = 28`, `log_3 28 = 3 = bump 2 (log_2 5)`.
example : Nat.log 3 (bump 2 5) = bump 2 (Nat.log 2 5) := by native_decide
-- `log_le_log_pred_succ`: one decrement lowers a log by ≤ 1 (`log_3 9 = 2`, `log_3 8 = 1`).
example : Nat.log 3 9 ≤ Nat.log 3 8 + 1 := by native_decide
-- `leadExp_drop_le_one`: leading exponent drops by ≤ 1 per step. `G(4,2)=41` (`log_4 41 = 2`),
-- `G(4,3)=60` (`log_5 60 = 2`): `2 ≤ 2 + 1`.
example : Nat.log (base 2) (goodsteinSeq 4 2) ≤ Nat.log (base 3) (goodsteinSeq 4 3) + 1 := by
  native_decide
-- `log_bump_pred_of_not_pow`: NO drop at a non-pure-power step. `n=5` (`2²=4 < 5`, not a pure
-- power): `bump 2 5 = 28`, `28−1 = 27`, `log_3 27 = 3 = bump 2 (log_2 5) = bump 2 2 = 3`. No drop.
example : Nat.log 3 (bump 2 5 - 1) = bump 2 (Nat.log 2 5) := by native_decide
-- the hypothesis is LOAD-BEARING: at a pure power `n=4=2²` the leading exponent DOES drop.
-- `bump 2 4 = 27`, `27−1 = 26`, `log_3 26 = 2 ≠ 3 = bump 2 (log_2 4)` — a genuine "borrow".
example : Nat.log 3 (bump 2 4 - 1) ≠ bump 2 (Nat.log 2 4) := by native_decide
-- `log_bump_pred_of_pow`: at the pure power `n=4` the drop is by EXACTLY one:
-- `log_3 26 = 2 = bump 2 (log_2 4) − 1 = 3 − 1 = 2`.
example : Nat.log 3 (bump 2 4 - 1) = bump 2 (Nat.log 2 4) - 1 := by native_decide
-- `ppCount`: `G(4,0)=4=2²` is a pure power (counts), `G(3,0)=3` is not (`2¹=2≠3`).
example : ppCount 4 1 = 1 := by native_decide
example : ppCount 3 1 = 0 := by native_decide
-- the sharpened telescope `leadExp_ge_sub_ppCount`, witnessed: `log_2 4 = 2 ≤ log_3 26 + ppCount 4 1
-- = 2 + 1 = 3`. A vacuous/backwards bound would fail this.
example : Nat.log 2 4 ≤ Nat.log (base 1) (goodsteinSeq 4 1) + ppCount 4 1 := by native_decide
-- `bump_eq_of_lt`: a single digit below its base is fixed (`bump 5 3 = 3`, `3 < 5`).
example : bump 5 3 = 3 := by native_decide
-- `leadExp_small_nonincreasing`: in the small regime the leading exponent only falls. `G(2,0)=2`,
-- `log_2 2 = 1 < base 0 = 2` (small); `G(2,1)=2`, `log_3 2 = 0 ≤ 1`. Non-increasing.
example : Nat.log (base 1) (goodsteinSeq 2 1) ≤ Nat.log (base 0) (goodsteinSeq 2 0) := by native_decide

-- the super-linear bound's interpretation, witnessed: `f_2(n) = 2^n·n` (`fastGrowing_two`), and the
-- step index `Nat.log 2 8 = 3` ⟹ the bound reads `f_2(3) = 24 ≤ goodsteinLength 8 + 2` (RHS huge).
example : fastGrowing 2 3 = 2 ^ 3 * 3 := by native_decide  -- = 24
example : Nat.log 2 8 = 3 := by native_decide

-- `bump_mono`: monotone in its argument. `bump 2 3 = 4 ≤ bump 2 5 = 10`.
example : bump 2 3 ≤ bump 2 5 := by native_decide
-- `leadExp_step_ge`: the per-step floor `bump(base k)(L_k) − 1 ≤ L_{k+1}`. At `m=4, k=2`:
-- `bump 4 2 − 1 = 1 ≤ log_5 54 = 2` (with `G(4,2)=41`, `L_2 = 2`, `G(4,3)=54`, `L_3 = 2`).
example : bump (base 2) (Nat.log (base 2) (goodsteinSeq 4 2)) - 1
    ≤ Nat.log (base 3) (goodsteinSeq 4 3) := by native_decide
-- `leadExp_ge_goodsteinSeq_log` (self-similarity): the leadExp sequence dominates the one-level-down
-- Goodstein sequence. `goodsteinSeq (log₂ 4 = 2) 2 = 1 ≤ log_4 41 = 2`. A backwards bound would fail.
example : goodsteinSeq (Nat.log 2 4) 2 ≤ Nat.log (base 2) (goodsteinSeq 4 2) := by native_decide
-- `two_le_goodsteinSeq`: a term stays `≥ 2` until two steps before it terminates.
-- `goodsteinLength 3 = 5`; at `k = 2` (`2+1 < 5`) the value `goodsteinSeq 3 2 = 3 ≥ 2`.
example : 2 ≤ goodsteinSeq 3 2 := by native_decide
example : fastGrowing 0 2 ≤ goodsteinLength 2 + 2 := by native_decide  -- 3 ≤ 5
example : fastGrowing 1 2 ≤ goodsteinLength 2 + 2 := by native_decide  -- 4 ≤ 5
example : fastGrowing 0 3 ≤ goodsteinLength 3 + 2 := by native_decide  -- 4 ≤ 7
example : fastGrowing 1 3 ≤ goodsteinLength 3 + 2 := by native_decide  -- 6 ≤ 7

end Goodstein.Dom
