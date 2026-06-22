# HANDOFF — 2026-06-22 (lap 10)

> **Branch** `plan` · **HEAD** = latest (8 commits this lap) · build **green**
> (`lake build GoodsteinPA`, 1257 jobs) · headline `peano_not_proves_goodstein` = honest `sorry`
> (0 math axioms) · working tree clean.
> **Lap 10 closed the truth-layer gap: the M5 `axTrue` surgery is DONE — `Z∞` now has the
> atomic-truth axiom + a truth-layer cut-elimination, axiom-clean. M5 can now host the embedding.**
> Read `ANALYSIS-2026-06-22-truth-layer-gap.md` for context, then "NEXT LAP" below.

## 🎯 NEXT LAP — `embedC` `axm` + `exs` (the last two cases; both unblocked by `axTrue`)
The **assignment-carrying embedding `embedC`** (`wip/Embedding.lean`) is the correct frame and is
**8/10 DONE** (lap 10): `∃ c, ∀ e:ℕ→ℕ, ∃ α, Provable α c (Γ.image (asg e ▹))`, `asg e := Rew.rewrite
(nm∘e)` closes all free vars → every sequent CLOSED. The cut rank `c` is hoisted out of `∀ e` (uniform
since `(asg e ▹ φ).complexity = φ.complexity`), which the `allω` ω-rule needs. **PROVED:** all 7
structural cases + **`all`** (the ω-rule, via `ih (n :>ₙ e)` + the `free → subst∘q` Rew identity).
Headline use: `embedC d` then `(fun _=>0)`; `↑gs` closed so `asg _ ▹ ↑gs = ↑gs`.

**Remaining (disclosed `sorry`, the deep content):**
- **`exs`** — `asg e ▹ t` is CLOSED (value `m`). Two steps: (i) `asg e ▹ (φ/[t]) = ((asg e).q ▹ φ)/[asg
  e ▹ t]` (a clean Rew-substs lemma, like `rew_subst_nm` for general `t`); (ii) the **closed-term
  collapse** `Provable (insert (ψ/[s]) Γ) → Provable (insert (ψ/[nm m]) Γ)` for closed `s` of value `m`
  — needs Z∞ equality-congruence (`s = nm m` is a true closed atomic ⟹ `axTrue`, then Leibniz, which
  M5 lacks as a rule). THE term-evaluation content; build a `Provable.exI_closed` derived lemma.
- **`axm`** — closed PA axiom `↑σ`, `σ ∈ 𝗣𝗔⁻ ∪ InductionScheme`:
  - `𝗣𝗔⁻` (finite, enumerate Foundation's axiom set): strip `∀` via `allω`, decompose the propositional
    structure (`orI`/`andI`/`exI`), bottoming at true closed atomic literals → **`Provable.axTrue`**.
  - `univCl(succInd ψ)`: the worked meta-induction (PENDING_WORK lap-10 block) — `cut`/`exI`/`andI`/
    `provable_em`, with `nm n+1 = nm(n+1)` discharged via `axTrue` (same collapse as `exs`(ii)).
The naive `embed`/`provable_rew`/`shift`/`all` (same file) are **superseded** — reference only
(`provable_rew` carries a disclosed `sorry` on its `axTrue` case; renaming invariance is false there).

## ✅ The M5 `axTrue` surgery (lap 10, COMPLETE, committed, axiom-clean)
`src/GoodsteinPA/Zinfty.lean`. Added the ω-logic atomic-truth leaf + truth-layer cut-elim:
- `signedLit b r v` (Bool-signed literal), `LitTrue` (ℕ-truth), `litTrue_neg`/`_or_neg`/`_flip`.
- **`Deriv.axTrue`** constructor (`o=cr=0`) + `Provable.axTrue` smart constructor.
- Threaded all 9 recursion sites (`o`, `cr`, `orInvAux`, `allInvAux`, `andInvAux`, `cutReduceAllAux`,
  `removeFalsumAux`, `cutElimStepAux`, `atomCutAux`).
- **`removeFalseLitAux`**: remove any FALSE closed literal from a cut-free derivation (truth layer).
- **`atomCutAux`**: splits on `litTrue_or_neg` of the cut atom (true ⟹ `removeFalseLitAux` the false
  `∼`-side off `hNC`; false ⟹ existing set-idempotence).
- `#print axioms Provable.cutElim = [propext, Classical.choice, Quot.sound]` — NO `sorryAx`, NO math
  axioms. M5 stays clean (`Classical.choice` already in the ledger). `LowerBound` untouched.

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
4. **M5 `axTrue` surgery COMPLETE** (see below) — `Z∞` now hosts the embedding, axiom-clean.

## State of the spine (Route B, two-phase)
- **M1, M2, Phase 0/1** — done, clean. M1 (`Encoding.goodsteinTerminates_re` → `Computable bump`) is
  **already discharged** (`Computability.lean` sorry-free) — the operator's "discharge M1" is done.
- **M5 — ε₀ cut-elim + truth layer** (`src/Zinfty.lean`) — done, clean. The lap-10 `axTrue` surgery
  added the ω-logic atomic-truth leaf so M5 now hosts the embedding (was pure-logic before).
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
## Lap-10 changes (8 commits)
- `src/GoodsteinPA/Zinfty.lean` — **`axTrue` truth-layer surgery** (the headline): `signedLit`/
  `LitTrue`/duality, `Deriv.axTrue` + `Provable.axTrue`, 9 sites threaded, `removeFalseLitAux` +
  `atomCutAux` truth split. Green, axiom-clean (`cutElim = [propext, choice, Quot.sound]`).
- `wip/Embedding.lean` — `rew_subst_nm` proved; `embed` naive `shift`+`all` proved (now SUPERSEDED by
  the assignment form); `provable_rew` carries a disclosed `sorry` on its `axTrue` case (the pivot).
- `ANALYSIS-2026-06-22-truth-layer-gap.md` — NEW (the finding + resolution; now executed).
- `wip/ZinftyTrue.lean` — created then **promoted into `src/` and removed** (content lives in Zinfty).
- `PENDING_WORK.md` — lap-10 block (worked `axm` paper proof + truth-layer gap). Update for the
  assignment-form pivot next.
- `STATUS.md` / `HANDOFF.md` — refreshed. Build green (1257), headline `sorry` intact.
