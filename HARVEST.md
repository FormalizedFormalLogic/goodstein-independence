# HARVEST — reusable spin-offs from the GoodsteinPA expedition 🌾

> Catalog of self-contained, axiom-clean results this campaign produced that have value **independent
> of the headline** (`peano_not_proves_goodstein`). Each entry: what it is, where it lives, its verified
> `#print axioms`, and a candidate destination (mathlib / Foundation / a standalone gallery note).
> Maintained on review/reflection laps. *Verify the `#print axioms` line before trusting any entry —
> re-run, don't copy.* (Created lap 62, 2026-06-24.)

## Tier 1 — banked monuments (DONE, axiom-clean, publishable as-is)

### `Thm56.peano_not_proves_TI` — Gentzen 1943 sharpness: `𝗣𝗔 ⊬ TI(ε₀)`
- **What:** Peano Arithmetic does not prove transfinite induction up to ε₀ (free-predicate form), via the
  full Buchholz Ω-rule infinitary apparatus (`embedC` embedding + cut-elimination + boundedness Thm 5.4).
- **Where:** `src/GoodsteinPA/Thm56.lean` (+ `Zinfty`, `ZinftyGen`, `XFreeCutElim`, `Embedding`,
  `Boundedness`, `Hardy`, `Domination`, `EmbeddingBound`, `EmbeddingX` — ~15-lap monument).
- **`#print axioms`:** `[propext, Classical.choice, Quot.sound, ONoteComp.cmpStep_spec._native.native_decide.ax_1_5]`
  (lap-62 verified) — trust base + one 🟢 finite `native_decide` artifact. CLEAN.
- **Why off-headline:** free-X-TI ⊢ PRWO is the *wrong direction* for `γ→Con` (lap-45/53 finding). It is a
  real, banked, standalone result — **do NOT delete, do NOT resurrect as the back-end.**
- **Destination:** standalone Lean gallery / Foundation contribution (Gentzen's PA-unprovability of TI(ε₀)).
  Largest reusable asset in the repo.

## Tier 2 — internal ε₀ arithmetic over `V ⊧ 𝗜𝚺₁` (axiom-clean infrastructure, broadly reusable)

These formalize **ordinal notation arithmetic *inside* a model of arithmetic** — rare and reusable for any
internalized-proof-theory or reverse-math project. All `[propext, choice, Quot.sound]` (spot-verify per use).

### `InternalONote` — internal Cantor-normal-form ε₀ codes + transparent comparison `icmp`
- **Where:** `src/GoodsteinPA/InternalONote.lean` (2317 lines). The transparent ε₀ order `icmp : V→V→V`
  (lap-56 key: transparent, not opaque `precφ`), NF predicate `isNF`, `ocOadd`/`ocExp`/`insTerm`.
- **Destination:** the substrate for any "ε₀ inside `IΣ₁`" development; candidate Foundation contribution.

### `InternalNadd` — internal Hessenberg (natural) sum `#` with full order theory F1–F4
- **Where:** `src/GoodsteinPA/InternalNadd.lean` (1050 lines). `inadd`/`insTerm` on CNF codes; NF
  preservation; **F1** strict left-monotonicity, **F2** `ω^α#ω^β ≺ ω^γ`, **F3** `ω^β·k ≺ ω^{β+1}`, **F4**
  commutativity. = Buchholz Lemma 4.1's input.
- **Destination:** natural-sum algebra; pairs with mathlib's `Ordinal.nadd` as the *internalized* analogue.

### `InternalTower` — internal ω-exponential tower `ω_n(α)` with strict base-monotonicity
- **Where:** `src/GoodsteinPA/InternalTower.lean`. `iotower`, `icmp_iotower_mono`,
  `icmp_iotower_lt_succ_of_le` (the two Thm-4.2 descent template engines).
- **Destination:** with `InternalNadd`, the Buchholz `o(d)=ω_{dg(d)}(õ(d))` assignment kernel.

### Crux-1 internal Grzegorczyk / Cor-3.4 substrate (Rathjen §3, standard level)
- **Where:** `BlkRec`/`BlkRecF` (block bookkeeping over a width **function**), `StdCor34`/`StdCor34F`
  (`crux1_internal_run_F`, axiom-clean), `InternalThm35`, `InternalGrz`, `IIter`, `Grzegorczyk` (ℕ-template,
  sorry-free). The whole `γ → PRWO(ε₀)` reduction (crux 1) is **fully proved, axiom-clean** (lap 57).
- **Destination:** internalized fast-growing/Grzegorczyk hierarchy; reusable for other independence results
  routed through Rathjen-style slow-down arguments.

## Tier 3 — faithfulness anchors (small, locked, exemplary)

### `goodsteinSentence_faithful` — the encoding-correctness bridge
- **Where:** `src/GoodsteinPA/Bridge.lean`. `(ℕ ⊨ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq m N = 0`.
- **`#print axioms`:** `[propext, choice, Quot.sound]` (lap-62 verified). CLEAN.
- **Value:** the template for "syntactic sentence ↔ semantic statement" audit surfaces.

## Maintenance
- Re-verify every `#print axioms` line on each review lap (assignment/order files are still under active
  edit; a regression would surface here first).
- When crux 2 lands, add: the arithmetized system-Z ordinal assignment (`InternalZ`), the Foundation→Z
  bridge (C0.5), and the internalized Gentzen `PRWO(ε₀) → Con(PA)` (a standalone headline in its own right,
  per the operator's "may state+prove PRWO→Con separately" allowance).
