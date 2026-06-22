# HANDOFF — 2026-06-22 (lap 9, deep-reflection lap)

> **Branch** `plan` · **HEAD** `1f32e49` (+ this lap's reflection commit) · build **green**
> (`lake build GoodsteinPA`, 1257 jobs) · headline `peano_not_proves_goodstein` = honest `sorry`
> (`#print axioms` = `[propext, sorryAx, choice, Quot.sound]`, 0 math axioms) · working tree clean.
> **This was a deep-reflection lap: it COURSE-CORRECTED the campaign. Read `REFLECTION-2026-06-22.md`
> first, then `STATUS.md`.**

## ⏭️ NEXT LAP — FIRST ACTION (the course change)

**Read `REFLECTION-2026-06-22.md` + `STATUS.md` ("Where it stands" + Outstanding §1–4).** Then:

**Attack M4 — the embedding `𝗣𝗔 ⊢ φ ⟹ Z_∞ ⊢^{α}_c {φ}`.** This is the highest-value target: the
**universal bottleneck** (required on every route to the headline) and untouched since lap-6 recon.

**Do NOT resume the witness-bounded cut-elim thread** (`cutReduceAllAux`, `Zekd`, any 4th index
calculus). The lap-8 findings + the cross-lap landscape memory both prove it is **off the critical
path** (single-index Hardy inequality is false; M5's witness-FREE cut-elim, done since lap 3, is what
the headline path uses, as-is). `wip/{BoundedZinfty,SplitZinfty,OperatorZinfty}.lean` are now
**reference only** — never the headline path.

### Concrete M4 plan (next lap)
1. **Read Foundation's finitary `Derivation`** — its definition, constructors, and recursor/induction
   principle (the Tait-style sequent calculus for `ℒₒᵣ` PA that backs `𝗣𝗔 ⊢ φ`). Find where `𝗣𝗔 ⊢ φ`
   unfolds to a `Derivation`.
2. **Write the embedding skeleton** `embed : 𝗣𝗔 ⊢ φ → ∃ α c, ZinftyF.Provable α c {φ-image}` by
   induction on `Derivation`. The **structural** rules port to existing `ZinftyF.Provable.*`
   constructors (`axL`/`verumR`/`andI`/`orI`/`cut`, see `src/Zinfty.lean:144–238`). Get those green.
3. **Isolate the crux** = **finite induction axiom → ω-rule** (`Provable.allω`, `src/Zinfty.lean:183`).
   This is the lap-6 "derivation-substitution" 2nd-deep-case. Leave it as the single disclosed `sorry`.
   That alone is a clean feasibility readout on Route B's deepest unknown — a successful lap.
4. If M4 hits a Foundation-`Derivation` wall, **pivot to M7a** (parallel/fallback, shovel-ready):
   transparent `gAllReal = ∀x∃y[g_y(x)=0]` (arithmetize `goodsteinSeq` via Foundation Σ₁ tools) +
   `𝗣𝗔 ⊢ goodsteinSentence ↔ gAllReal`, **gated by `Bridge.lean`'s spec** so faithfulness can't regress.

### Then (downstream, not next-lap)
- **Bounding bridge** (small once M4 + M7a land): prove `cut-free Provable α 0 Γ` (Γ in the g-fragment)
  ⟹ ∃-witness `≤ hardy (toONote α) N` by induction on the cut-free `Deriv` (`allInv` the ∀ away, read
  the `exI` numeral off — no `+α` growth), combine with M6's `hardy_lt_goodsteinLength`
  (`src/LowerBound.lean:258`) ⟹ `False`. **Prove on M5's real `Deriv` directly**; reuse M6's
  ℕ-domination fact, NOT the abstract `B` transport (the `B` lower bound is the template, banked).
- **Ordinal seam**: M5 cut-free `α : Ordinal.{0}` (`<ε₀`) → M6 `ONote` `hardy`. Either `∀ α<ε₀, ∃ o,
  o.NF ∧ o.repr=α` (check mathlib for `ONote.repr` surjectivity onto `[0,ε₀)`) or restate the bounding
  lemma's ordinal in `ONote`. Light — one `toONote` at the leaf, not a calculus rebuild.
- **Assembly (M7b)** → discharge the headline `sorry` **only** when `#print axioms` is clean and it
  genuinely chains (anti-fraud, `DIRECTION.md`).

## State of the spine (Route B, two-phase, corrected priorities)
- **M1, M2, Phase 0/1** — done, clean. (`Encoding`/`Bridge`/`Reduction`/`Computability`/`Defs`.)
- **M5 — witness-FREE ε₀ cut-elim** (`src/Zinfty.lean`, `Deriv.Provable.cutElim`) — done, clean. Used
  **as-is** on the two-phase path; the embedding skeleton's structural cases mirror its constructors.
- **M6 — Hardy lower bound** (`src/LowerBound.lean`, `lowerBound_hardy_selfcontained`) — done, clean.
  Reusable core = `hardy_lt_goodsteinLength` (ℕ-domination). The `B` calculus = banked template.
- **M4 — embedding** — THE live target. Untouched. Feasibility-gating.
- **M7a — transparent arithmetization** — parallel/fallback thread, shovel-ready, faithfulness-gated.
- **Bounding bridge + assembly (M7b)** — downstream, small once M4 + M7a land.
- **BANKED, do NOT resume:** `wip/{BoundedZinfty,SplitZinfty,OperatorZinfty}.lean` (witness-bounded
  cut-elim, off critical path). **Route A** (`Reduction.goodstein_implies_consistency`, via `Con(PA)`)
  = escape hatch only; re-introduces `PA_delta1Definable` (🟡) and also needs M4.

## Notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`. Headline `sorry` intact.
- **`WebFetch` dead in box; `WebSearch` works.** No open `ON-LINE-REQUEST.md` (all answered; the three
  findings are harvested into `archive/findings/`). File a new one only for a genuine literature gap.
- **Aristotle:** idle is correct — M4 needs Foundation's real `Derivation` internals (not cleanly
  self-containable); M7a is arithmetization over Foundation's API (same). Feed only a genuinely-bounded,
  self-contained open lemma if one arises (e.g. an isolated `ONote.repr`-surjectivity statement).
- **Reference corpus** (`~/personal/claude/knowledge/core/projects/lean-journey/reference/`):
  `goodstein-independence-landscape.md` (the campaign map), `foundation-encode-predicate-via-codeOfREPred.md`,
  the ONote/Hardy gotcha files. `grep -rl <keyword>` before re-deriving any friction.

## Lap-9 changes (this lap)
- `REFLECTION-2026-06-22.md` — **NEW**: the deep-reflection synthesis (direction call, KEEP/STOP,
  highest-value target = M4, architecture insights).
- `STATUS.md` — refreshed (header lap 9, "Where it stands" course-correction, prepended dated bullet,
  reordered Outstanding to unavoidable-first, ledger re-confirmed by real `#print axioms`).
- `HANDOFF.md` — this rewrite (points next grind lap at M4; bans the Zekd thread).
- `PENDING_WORK.md` — prepended the lap-9 course-correction at top.
- No `src/` changes; build green (1257), headline `sorry` intact, ledger unchanged.
