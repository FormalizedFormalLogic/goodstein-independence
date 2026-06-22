# Pending work — open obligations & attack paths

State after lap 2026-06-22. Build green (`lake build GoodsteinPA`, 1204 jobs). Phase 0 (encoding +
faithfulness bridge) axiom-clean. Phase 1 (Gödel II hook) landed. The headline stays a literal
`sorry` (anti-fraud). See `PHASE2-DECOMPOSITION.md` for the full girder ladder.

## Open obligations (toward a clean headline)

### O1 — `Reduction.goodstein_implies_consistency` (Route A girder) — `sorry`
`𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`. The deep ordinal-analysis content via Con(PA).
Attack paths:
1. **Gentzen `TI(ε₀) ⊢ Con(𝗣𝗔)` + `γ ⟹ TI(ε₀)`** — the classic route; needs `PA_∞`
   cut-elimination (same `Z_∞` machinery as Route B) plus the Con(PA) lower bound. Reuses
   Foundation's Gödel II downstream. (Buchholz `on-gentzens-first-consistency-proof`.)
2. **Drop Route A entirely for Route B** (recommended) — Towsner shows `𝗣𝗔 ⊬ γ` directly without
   Con(PA); then `goodstein_implies_consistency` becomes unnecessary (leave it as a documented,
   never-used alternative). The headline is discharged via O2's chain instead.
3. Partial: keep the lemma but prove the *easier* converse direction / a weaker reflection
   principle first as warmup, to exercise Foundation's provability API (`⊢`, `Con`, D1–D3).

### O2 — the Phase-2 girder (Route B, Towsner) — milestones M3…M7 in `PHASE2-DECOMPOSITION.md`
This is the real frontier. **Crux: M3 (`Z_∞` calculus) and M5 (cut elimination).**
Attack paths:
1. **Continue the `wip/Zinfty.lean` prototype** (E2 encoding — *compiles*). Next: (a) connect
   `AForm` to a faithful arithmetic formula with a real free-variable/substitution layer (replace
   the `ℕ → AForm` family with a single body + numeral substitution), so `rk` is genuinely
   finite; (b) state M3.3 bound-monotonicity lemmas; (c) state M4 embedding + M5 cut-elimination
   theorems as disclosed `sorry`s. Bank each as it typechecks; promote to `src/` when green.
2. **Develop M6 (Hardy domination) via Track 1.** `~/src/lean-formalizations` `Logic/FastGrowing`
   is building `h_α`, monotonicity, and Goodstein-length domination on mathlib's
   `ONote.fastGrowing`. Reuse those for M6.1–M6.3; only M6.4 (Thm 17.1, the cut-free lower bound)
   is new here. (Does NOT block M3–M5 — parallelizable.)
3. **Tackle cut-elimination (M5) on the prototype first**, before the embedding — it is the
   self-contained heart (Towsner §19). **STATUS: M5 is now structured down to ONE leaf.**
   `wip/Zinfty.lean` has `Provable.cutElim` (Thm 19.9, full elimination) *proved* by induction on
   cut rank, reducing entirely to the single open lemma **`Provable.cutElimStep`** (Thm 19.7, one
   level). So the next concrete target is exactly `cutElimStep` = §19 inversions 19.2–19.4 +
   reductions 19.5–19.6 + the principal-`Cut`-on-rank-`c` case. Proving it makes the whole
   cut-elimination machine-checked (mod the embedding M4 and lower bound M6.4). NOTE: `cutElimStep`
   likely needs the numeric/Hardy `k` bound that `Provable` currently elides — re-add a `k : ℕ`
   index to `Provable`/`Deriv.o` first (it threads the `h_{ω^α}(k)` bound through 19.6/19.7).

### O3 — `PA_delta1Definable : 𝗣𝗔.Δ₁` (Foundation axiom) — only on Route A
Needed to *state* Gödel II for `𝗣𝗔`; Foundation axiomatizes it (TODO in
`Incompleteness/Examples.lean`). Route B avoids it. Attack paths:
1. **Avoid** — go Route B (O1 path 2); the axiom never enters the headline profile.
2. Discharge it: construct the Δ₁-definition of PA's axiom set (PA⁻ + induction scheme) in
   Foundation's `Theory.Δ₁` framework and prove `isDelta1`. Deep arithmetization; multi-lap.
3. Upstream: check whether a newer Foundation rev proves it (the TODO may get filled upstream);
   file an `ON-LINE-REQUEST.md` to check the latest Foundation `Incompleteness/Examples.lean`.

## Done this lap
- M1: `Encoding.goodsteinTerminates_re` proved (`Computability.lean`: `primrec_natLog`,
  `primrec_bump`, `primrec_goodsteinSeq`). Phase 0 axiom-clean.
- M2: `Reduction.lean` — Gödel II hook + meta-reduction (axiom-clean mod `PA_delta1Definable`).
- Phase 2: `PHASE2-DECOMPOSITION.md` (Towsner-grounded ladder) + `wip/Zinfty.lean` (E2 encoding
  prototype — compiles: ω-rule inductive, ordinal/cut-rank measures, bound-domination lemma,
  `Provable.mono`/`.weakening`, and the **proved predicate-level inference API** `Provable.orI`,
  `.exI`, `.allI` — the ω-rule with the supremum ordinal bound, machine-checked against the
  `Deriv` measures via `Classical.choice`).

## Design note — `Provable.cut` + the `ℕ∞` cut-rank (next lap, read before refactoring)
`cr : Deriv Γ → ℕ∞` (cut rank can be `⊤` for pathological infinite families). A predicate-level
`Provable.cut` is the one rule still missing: from `Provable α c (φ ::ₘ Γ)` and
`Provable β c (φ.neg ::ₘ Γ)` it should give `Provable (max α β + 1) c' (Γ)` where
`c' ≥ rk φ + 1`. But `rk φ : ℕ∞` may be `⊤`, so you can't pick a finite `c' : ℕ` in general —
`Provable`'s `c : ℕ`. **Fix:** when `AForm` gets the real free-variable + numeral-substitution
layer (the M3.1 refinement), `rk φ` becomes provably finite (`rk φ ≠ ⊤`) for genuine formulas, so
`Provable.cut` and the Hardy-bounded `cutElimStep` both become stateable with finite `c`. So the
substitution-layer refactor is a prerequisite for *both* `cut` and `cutElimStep` — do it first.

## Gotcha noted (for the corpus)
For `Ordinal`, `add_le_add_right h c` elaborates to `c + a ≤ c + b` (adds on the *left*) — use
`add_le_add h le_rfl` to get `a + 1 ≤ b + 1` from `a ≤ b`. `gcongr` on `⨆`-bounds spawns a
`BddAbove (Set.range …)` side-goal (discharge with `Ordinal.bddAbove_range`).
