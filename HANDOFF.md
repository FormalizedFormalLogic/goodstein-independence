# HANDOFF — 2026-06-22 (lap 10)

> **Branch** `plan` · **HEAD** `c253471` (5 commits this lap) · build **green**
> (`lake build GoodsteinPA`, 1257 jobs) · headline `peano_not_proves_goodstein` = honest `sorry`
> (0 math axioms) · working tree clean.
> **Lap 10 finished the M4 renaming enabler axiom-clean, drove `embed` to 8/10, and UNCOVERED + banked
> the campaign-critical "truth-layer gap": M5's pure-logic Z∞ cannot host the embedding as-is.**
> Read `ANALYSIS-2026-06-22-truth-layer-gap.md` FIRST, then this file's "NEXT LAP".

## ✅ Lap-10 results (all committed, green)
1. **`rew_subst_nm` PROVED** (`9531777`) → the M4 enabler `provable_rew` + `ZProvable.rew` are now
   **fully axiom-clean** (`[propext, choice, Quot.sound]`, 0 math axioms). `wip/Embedding.lean`.
2. **`embed` `shift` + `all` PROVED** (`6eb1f03`) → **8/10 cases** (only `axm`, `exs` remain).
   - `shift` = `ZProvable.rew Rew.shift`.
   - `all` = the **ω-rule case**: `provable_rew` substitutes the freed var by each `nm n` (which
     simultaneously undoes the `shift` on `Γ` via `Rew.rewrite_comp_shift_eq_id`), then `Provable.allω`.
3. **ANALYSIS — the truth-layer gap** (`624933e`): `ANALYSIS-2026-06-22-truth-layer-gap.md`. The
   finding (grounded in the code): every PA axiom embedding (`axm`) bottoms out at **true closed
   atomics** (`nm n + 0 = nm n`; and the successor bridge `nm n + 1 = nm(n+1)`). M5's `Deriv` is pure
   logic — only atomic leaf is `axL` (both polarities); its atomic cut-elimination is **deliberately
   truth-free** (header line 15, `atomCutAux` docstring). Adding a one-polarity `axTrue` breaks that.
   The sibling `LowerBound.B` calculus **already has `trueR`**, and the planned bounding bridge maps
   `Deriv` leaves to `B.trueR` — so the architecture already presupposes `axTrue` on `Deriv`.
4. **Truth-layer semantic core** (`c253471`): `wip/ZinftyTrue.lean`, axiom-clean. `LitTrue` (ℕ-truth
   of a closed literal) + `litTrue_neg` (∼-duality, `@[simp]`) + `litTrue_or_neg` (totality) +
   `not_litTrue_and_neg`. Constructor-independent; the surgery's leaf/atomic-cut cases consume these.

## ⏭️ NEXT LAP — the M5 `axTrue` surgery (THE crux; contained to `src/GoodsteinPA/Zinfty.lean`)
Plan in `ANALYSIS-2026-06-22-truth-layer-gap.md §Resolution`. Blast radius = **one file** (`Deriv` is
used only in `Zinfty.lean`; `LowerBound.B` is separate). Adding the constructor reds **all 9** `Deriv`
recursion sites at once → it is an all-or-nothing green push (do it in one focused lap; don't half-land
it in `src/`). Steps:
1. **Move `LitTrue` + lemmas from `wip/ZinftyTrue.lean` into `Zinfty.lean`** (before `Deriv`).
2. **Add constructor** `axTrue {Γ} (L) (htrue : LitTrue L) (hmem : L ∈ Γ) : Deriv Γ`. `o = 0`, `cr = 0`.
3. **Trivial mirror cases** (≈ the `axL` case — true literal survives every erase/insert, re-apply
   `axTrue`): `o` (l.90), `cr` (l.104), `orInvAux` (l.244), `allInvAux` (l.377), `andInvAux` (l.498),
   `cutReduceAllAux` (l.791), `cutElimStepAux` (l.1267).
4. **The truth layer (the real work, concentrated):**
   - **Generalize `removeFalsumAux` (l.1123, removes `⊥`) → `removeFalseLiteralAux`** (removes any
     *false* closed literal `L`, `¬LitTrue L`, bound-preserving). Body ≈ copy of `removeFalsum` + two
     leaf cases: `axTrue` (removed `L` false ≠ true axiom literal ⟹ survives) and `axL` (if `L` is one
     clash polarity, the partner is *true* ⟹ close by `axTrue` on the partner). `verumR`: `⊤` is true
     so `⊤ ≠ L`. Use `litTrue_neg`/`litTrue_or_neg`.
   - **`atomCutAux` (l.1011): split on `litTrue_or_neg (rel r v)`.** True ⟹ `nrel r v` (=`∼`) is false
     ⟹ `removeFalseLiteralAux` it off `hNC`. False ⟹ the existing set-idempotence argument. Plus an
     `axTrue` case in the structural induction on `d` (mirror; the `L = rel r v` subcase routes through
     `removeFalseLiteralAux` on `hNC`).
5. **Re-verify**: `lake build GoodsteinPA` green; `#print axioms Provable.cutElim` (now also depends on
   `Classical.choice` via `LitTrue` totality — that is fine/expected, NOT a math axiom). LowerBound
   untouched.

**Then `axm` becomes provable** (worked paper proof in `PENDING_WORK.md` lap-10 block):
- `σ ∈ 𝗣𝗔⁻` (PeanoMinus, finite): strip `∀` via `allω` → each closed instance is a true atomic → `axTrue`.
- `σ = univCl(succInd ψ)`: `allω`-stripped + meta-induction on `n` (`cut` on `ψ(n)`, `exI` witness,
  `andI`, `provable_em`), with the `nm n+1 = nm(n+1)` step now dischargeable via `axTrue`.

**Then `exs`** (last): the assignment-carrying reformulation `embed : ∀ e:ℕ→ℕ, ZProvable (Γ.image (ρe ▹))`,
`ρe := Rew.rewrite (nm∘e)` (closes free vars to numerals); re-proves the 8 done cases (mechanical, ρe
distributes); `exs` evaluates `ρe▹t` (closed) to its numeral via the `axTrue` closed-term collapse.

## State of the spine (Route B, two-phase)
- **M1, M2, Phase 0/1** — done, clean. M1 (`Encoding.goodsteinTerminates_re` → `Computable bump`) is
  **already discharged** (`Computability.lean` sorry-free) — the operator's "discharge M1" is done.
- **M5 — ε₀ cut-elim** (`src/Zinfty.lean`) — done, BUT **pure-logic; needs the `axTrue` surgery above**
  to host M4. (This is the lap-10 finding; M5's stated cut-elim theorem is fine, the calculus was
  under-specified for the embedding.)
- **M6 — Hardy lower bound** (`src/LowerBound.lean`, `lowerBound_hardy_selfcontained`) — done, clean.
  Uses the **separate** abstract `B` calculus (which already has `trueR`); untouched by the surgery.
- **M4 — embedding** (`wip/Embedding.lean`) — enabler axiom-clean; 8/10; `axm`/`exs` blocked on the
  surgery. **`provable_em` still promotable to `src/Zinfty.lean`** (axiom-clean, lap-9).
- **Bounding bridge + assembly (M7b)** — downstream.

## Notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`. Headline `sorry` intact.
- **`WebFetch` dead; `WebSearch` works.** No open `ON-LINE-REQUEST.md`.
- **Aristotle:** idle is correct — the surgery is over M5's real `Deriv` internals (not cleanly
  self-containable). Feed only a genuinely-bounded isolated lemma if one arises.
- **Reference corpus** (`~/personal/claude/knowledge/core/projects/lean-journey/reference/`):
  `goodstein-independence-landscape.md`, the ONote/Hardy gotcha files. `grep -rl <keyword>` first.
- **Pacing:** lap wrapped at a clean green checkpoint (5 commits) rather than half-landing the
  multi-hundred-line surgery in `src/` (per memory `pacing-checkpoint-then-check-governor`).

## Lap-10 changes
- `wip/Embedding.lean` — `rew_subst_nm` proved; `embed` `shift`+`all` proved (8/10); header refreshed.
- `ANALYSIS-2026-06-22-truth-layer-gap.md` — NEW (the finding + resolution plan).
- `wip/ZinftyTrue.lean` — NEW (truth-layer semantic core, axiom-clean).
- `PENDING_WORK.md` — prepended lap-10 block (worked `axm` paper proof + the truth-layer gap).
- `STATUS.md` / `HANDOFF.md` — refreshed. No `src/` changes; build green (1257), headline `sorry` intact.
