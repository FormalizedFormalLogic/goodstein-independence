# HANDOFF — re-home goodstein onto upstream Foundation (retire the fork)

> **STATUS 2026-07-04: COMPLETE (in-box).** Bare `lake build` is GREEN (1345 jobs) and
> `#print axioms GoodsteinPA.peano_not_proves_goodstein` reports EXACTLY
> `[propext, Classical.choice, Quot.sound]` — no new axioms/sorries above baseline (verified via
> `lake env lean` since the box has no `lean-axiom-gate`). The 15 pre-existing governance-gated
> sorries (Embedding ×2, EmbeddingX ×2, E1EmbeddingGrind ×10, plus 1 elsewhere) are unchanged and
> off the headline. Trusted surface (Statement/Encoding/Bridge/Compat) untouched.
>
> The Derivation2 Schema→Theory port touched 8 files beyond the handoff's "15 errors" estimate
> (the estimate was measured before the build reached the downstream files): Embedding, EmbeddingX,
> EpsilonOrder, FvSubst, DescentLift (axm/Theory port), plus ReductModel, EmbeddingBound,
> E1EmbeddingGrind (ModelsTheory→ModelsSet/`models_lMap`, `+`→`∪`, `𝗘𝗤`→`𝗘𝗤 L`, `provable_def`/
> `Derivation.toDerivation2`→`provable_iff_derivable2`, and the upstream `∘`-composition simp-normal-form
> churn via `Function.comp_def`). Committed on `rehome-foundation-upstream`.
>
> **HOST ENDGAME (Trevor):** the box cannot push / run `cc`-native `blueprint_audit`. On the host:
> re-confirm `lean-axiom-gate --exact`, run `lake exe blueprint_audit`, push, open the
> `retire-foundation-fork` PR.

**Goal.** Repoint the `Foundation` dependency from the personal fork `gotrevor/Foundation @ e6e1ad14`
to **upstream `FormalizedFormalLogic/Foundation` (master `2040d2f3`)** and get `lake build` green +
axiom-clean, so `gotrevor/Foundation` can be retired. Branch: `rehome-foundation-upstream`
(worktree `~/src/goodstein-independence-rehome`, off `origin/main` `79f56ee`).

**Objective for the grind:** `mode=build-green`. Done ⇔ bare `lake build` green AND
`lean-axiom-gate --exact --target GoodsteinPA.peano_not_proves_goodstein` reports exactly
`[propext, Classical.choice, Quot.sound]` (no new axioms/sorries above baseline).

## Why the repoint isn't mechanical
The proof landed upstream, but upstream **refactored the Foundation API** during the Δ₁ PR review.
`lake update Foundation` (already applied — mathlib held at `fabf563a`/v4.31.0, +5 docs-only deps)
builds Foundation itself fine, but goodstein's 57k-line source was written against the fork's older
API spelling.

## What is DONE (mechanical ~90%, 313 → 15 errors)
Two durable artifacts do the bulk, deterministically:

1. **`src/GoodsteinPA/Compat.lean`** — anti-corruption shim. Every entry is an `abbrev` / `notation`
   / *proved* lemma (never an axiom), so `#print axioms` still machine-verifies faithfulness:
   - notation `⊧ₘ*` → `↓[ℒₒᵣ] ⊧*` (ModelsSet), `⊧ₘ` → `↓[ℒₒᵣ] ⊧` (Models)
   - `gEval`/`gVal` (fork's structure-**explicit** `Semiformula.Eval`/`Semiterm.val`; upstream made
     the `Structure` an instance), `gEvalm`/`gValm` (removed model-variants, `M` explicit)
   - re-proved removed arity lemmas: `eval_rel₀/₁/₂`, `eval_nrel₀/₁/₂` (Compat namespace),
     `Semiterm.val_operator₀/₁/₂` + `val_const`, `SyntacticSemiformula`/`SyntacticFormula`
     (restored into `LO.FirstOrder`)
2. **`scripts/rehome_foundation_api.py`** — deterministic, idempotent rewriter (dry-run default,
   `--apply` to write). Retargets removed/changed names to Compat, adds the shim import (module-file
   aware: skips Lean `module` files like `FvSubst.lean`), and appends `Function.comp_def` inside
   `simp`-family brackets (upstream changed the rel-vector simp normal form from `fun i => f (v i)`
   to `f ∘ v`) while stripping it from `rw` brackets. **Re-run it after any further edits.**

Key upstream facts already established (all greppable locally — the fork is cloned at
`~/src/Foundation @ e6e1ad14`, upstream is in `.lake/packages/Foundation`):
- `ORingStructure` unchanged. General `eval_*`/`val_operator`/`rew_*` lemmas kept (fire through the
  reducible abbrevs). `ModelsTheory` survives; `Rewriting.emb` survives.
- `Proposition L = Formula L ℕ = SyntacticFormula L` **definitionally** (all `Semiformula L ℕ 0`).
- Member-satisfaction lemma (replaces the removed `ModelsTheory.models`):
  `Semantics.models 𝓜 (hf : φ ∈ T) : 𝓜 ⊧ φ` (`Logic/Semantics.lean:182`), or
  `Semantics.modelsSet_iff.mp inferInstance hf`.

## What REMAINS — the architectural port (15 errors, faithfulness-sensitive)
Upstream **restructured `Derivation2`**: fork `Derivation2 (𝓢 : Schema L) : Finset (SyntacticFormula L)`
→ upstream `Derivation2 (T : Theory L) : Finset (Proposition L)` (`Calculus2.lean:13`). The index went
from a set of *formulas* (`Schema`) to a set of *sentences* (`Theory`); sequent element type is
defeq (`Proposition = SyntacticFormula`). `axm` changed: fork `axm (φ : SyntacticFormula) (φ ∈ 𝓢)`
→ upstream `axm (φ : Sentence) (φ ∈ T) ((φ : Proposition) ∈ Γ)`.

Already done toward this: 23 `: Schema L` → `: Theory L` annotation swaps; the `Schema` shim was
tried then removed (it mis-coerced `𝗣𝗔`→Schema when `Derivation2` wants a `Theory`).

Remaining errors and what each needs:
- **`Embedding.lean` 533/539/540** — the `embedC` `axm` case. `obtain ⟨σ, hσ, rfl⟩ := hφ` no longer
  applies (φ is now a `Sentence` directly, no `Rewriting.emb ''` unwrap); rework to use `φ` as the
  sentence, and replace `ModelsTheory.models ℕ hσ` with the `Semantics.models`/`modelsSet_iff` idiom.
- **`EmbeddingX.lean` 413/539/853/927** — `Membership (Form LX) (Theory LX)` and
  `HAdd (Theory LX) (Theory LX)`. The generic embedding lemmas (`embedC_LX_gen`, `embedC_LX_bdd`,
  …) abstract over an axiom **formula-set** with `φ ∈ 𝓢` for `φ : Form LX`; upstream's `Theory`-indexed
  `Derivation2` wants sentence membership. These need genuine rework — either carry the theory as a
  `Theory LX` and go through the `axm`-sentence path, or reconcile `paLX`'s formula-vs-sentence view.
  (`paLX` is used as `: Theory LX` in `ReductModel.lean`, so it IS a Theory.)
- **`DescentLift.lean` ~221** — uses `Schema.lMap` / `Theory.toSchema` (removed). Rework onto the
  `Theory` path.
- **`EpsilonOrder.lean` 94** — `rw` pattern miss (a `gValm` vs `Semiterm.val` / `∘` shape); likely a
  local `unfold`/`simp only [Compat.gValm]` or `Function.comp_def` at that site.
- **`FvSubst.lean` 103** — `Language.LORDefinable ?m` stuck (metavar). Module file (uses upstream
  spelling directly, no Compat import). Needs an explicit `(L := L)` / type annotation on the
  `𝚺₁-Function₄ … via …Graph` instance so `L` is determined before instance resolution.

## Faithfulness (the trusted surface — leave hanging off upstream directly)
`Statement.lean` (`𝗣𝗔 ⊬ ↑goodsteinSentence`), `Encoding.lean` (`goodsteinSentence`), and
`Bridge.lean` (`ℕ ⊨ goodsteinSentence ↔ terminates`) are the audit surface. They must reference
upstream `𝗣𝗔` / provability / satisfaction directly. The shim only touches proof internals. Final
check: `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## Fire (Trevor)
This is a `mode=build-green` job. Grind **this worktree directly** — `c-yolo` detects a linked
worktree and mounts its shared git common dir rw, so `git` works in the box (no clone needed; the
worktree already has the built CoW `.lake` + the committed WIP on this branch):

    lean-treadmill goodstein-independence-rehome --prompt "Finish the upstream-Foundation rehome: get bare \`lake build\` green and axiom-clean per HANDOFF-REHOME.md. Fix the Derivation2 Schema→Theory embedding-layer errors; keep the trusted surface (Statement/Encoding/Bridge) on upstream; re-run scripts/rehome_foundation_api.py after edits." --max-duration 4h --review-every 3

Endgame (host, after green): `lean-axiom-gate --exact`, commit, push, open the PR. The PR is the
`retire-foundation-fork` todo; retiring `gotrevor/Foundation` also waits on the other fork consumers.
