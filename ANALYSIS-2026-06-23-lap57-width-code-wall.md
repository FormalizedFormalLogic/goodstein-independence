# ANALYSIS lap 57 — the crux-1 width-code wall: a finite `wseq` cannot drive an infinite descent

## Summary
The crux-1 internal girder `StdCor34.crux1_internal_run_of_width_dom` (and the `SeqDominated`
packaging in `wip/GentzenCon.lean` that feeds it) takes the block width as a **single finite sequence
code `wseq : V`**, read by `znth wseq b`. **This packaging cannot be instantiated for the descents the
headline actually needs** — its hypothesis set is effectively unsatisfiable in the very (nonstandard)
models where crux 1 must fire. The width must instead be a **𝚺₁-definable total function `W : V → V`**.
The girder is still TRUE (vacuously), so nothing false is in the kernel — but it is a **dead architecture**:
crux 1 cannot be completed through it. This is the sharpened crux-1 target.

## The argument
`DescentSlowdown.nonterminating_of_slowdown` (the Lemma-3.6 engine consuming the slowed sequence `β'`)
requires, for **every** `k : V`:
- `hdesc : icmp (β' (k+1)) (β' k) = 0` (descent), and
- `hCanon : iCanon (k+1) (β' k)`, i.e. `iC (β' k) ≤ k+1` (the slowness bound).
Both are `∀ k : V` — the dominating bound `b k` must beat `igoodstein m₀ k` at every stage to conclude
`∀ k, 0 < igoodstein m₀ k`. So the slow-down `β' = bbeta K s (salpha … (BlkRec.blk wseq) …)` must be
NF + slowness-bounded + descending for **all** `k : V` — unboundedly many blocks.

`BlkRec.blk wseq j` advances via `boStep`, reading the current block width `znth wseq (blk)`. By
Foundation's `Seq.znth_prop_not`, `znth wseq b = 0` for `b ≥ lh wseq`. With width `0`, the step
condition `off+1 < 0` is false, so **every** step past the code rolls to a new block:
`blk wseq j = blk wseq (lh) + (j − threshold)` — i.e. `blk wseq j ∼ j` for large `j`.

The slowness route needs the C-bound `hβC : iC (β (blk wseq j)) ≤ Cβ + j` (Cor 3.4; via
`iC (β n) ≤ wsumc wseq n` + `wsumc_blk_le`). Past the code, `wsumc wseq` is constant (adding `0`s),
while `blk wseq j ∼ j` so `iC (β (blk wseq j)) ∼ iC (β j)`. A descending ε₀-sequence below a fixed
`α < ε₀` can have **unboundedly growing CNF complexity** `iC` (e.g. `ω^n ↓` below `ω^ω`), which is exactly
the case Cor 3.4 (the slow-down) exists to absorb — and which `SeqStdBounded` only bounds by the *growing*
`iF l₀ n`, not by `Cβ + n`. Hence `iC (β j) ≤ Cβ + j` fails for large `j`, so **no finite `wseq`
satisfies `hβC`** for a genuine complexity-growing descent. Nonstandard length `N` does not help: `j`
ranges over all of `V > N`.

## The fix — width as a 𝚺₁ function (mirrors the ℕ-template)
The sorry-free ℕ-template `Grzegorczyk.lean` already uses a width **function** `W : ℕ → ℕ`
(`corW β t = C (β (t+1))`), with `wsum W`/`widx`/`woff` and `C (β n) ≤ wsum (corW β) n`
(`C_le_wsum_corW`). The internal `BlkRec` should be re-stated the same way: a `𝚺₁`-definable
`W : V → V` read as `W (blk)` inside `boStep`, instead of `znth wseq (blk)`. Then the cumulative width
`wsumc` grows without bound (no code-length ceiling), `iC (β (blk j)) ≤ wsumc W (blk j) ≤ j`-style bounds
hold for all `j`, and width domination is `W n = iC (β (n+1)) ≤ iF l₀ (n+1) ≤ iF (l₀+1) n` (so
`l₀' = l₀+1`). For `W = fun t => iC (β (t+1))` everything is `𝚺₁` (β, `iC` are), so the slowed sequence
stays `𝚺₁`-definable.

### Concrete next steps
1. **`BlkRec` over a width function.** Add `blkF W`/`offF W` (a `𝚺₁` `boState` recursion reading
   `W (π₁ ih)`; the blueprint `succ` references `W`'s graph formula). Re-prove the four bookkeeping
   facts (`blk_succ_dich`/`off_succ_of_blk_eq`/`blk_add_off_le`/`off_succ_lt_width_of_blk_eq`) and the
   width-sum facts (`wsumc`, `wsumc_blk_le`, and the new `C_le_wsumc` = internal `C_le_wsum_corW`).
   Additive (new defs alongside the code-based ones) → `src/BlkRec.lean` stays green.
2. **Re-thread `StdCor34`.** `salpha`/`bbeta_of_igtTot_blkRec`/`crux1_internal_run_of_width_dom` switch
   `BlkRec.blk wseq` → `BlkRec.blkF W`; the width-domination hyp becomes `∀ n, W n ≤ iF l₀ n` (a
   function bound, satisfiable). `hβC` discharges via the new internal `C_le_wsumc`.
3. **`SeqDominated` (`wip/GentzenCon.lean`).** Replace `wseq Cβ : M` with `W : M → M`,
   `Cβ := iC (β 0)`, `W := fun t => iC (β (t+1))`; `seqDescent_dominated` then discharges `hβC`/width-dom
   directly from `hβdesc` + `hβbound` (no remaining width-existence gap).

## Status
- No false kernel content (the girder is vacuously true). `wip/GentzenCon.lean` green (2 expected sorries).
- This supersedes the lap-56/57 "remaining gap = build `wseq`/`Cβ`" framing: there is **no finite `wseq`**
  to build; the gap is the **`BlkRec`-over-function refactor** above.
