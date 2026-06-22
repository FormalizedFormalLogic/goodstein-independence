# HANDOFF — 2026-06-22 (lap 9, deep-reflection lap)

> **Branch** `plan` · **HEAD** `7e71a4a` (6 commits this lap) · build **green**
> (`lake build GoodsteinPA`, 1257 jobs) · headline `peano_not_proves_goodstein` = honest `sorry`
> (`#print axioms` = `[propext, sorryAx, choice, Quot.sound]`, 0 math axioms) · working tree clean.
> **This was a deep-reflection lap: it COURSE-CORRECTED the campaign (off the witness-bounded
> cut-elim detour, onto M4 — the universal embedding bottleneck) AND made machine-checked M4
> progress. Read `REFLECTION-2026-06-22.md` first, then `STATUS.md`. Forward file:
> `wip/Embedding.lean` (compiles; `provable_em` proved + axiom-clean; `embed` 6/10 cases).
> Next target: the M4 enabler `Provable.rew` (see "Next lap" below).**

## ⏭️ NEXT LAP — FIRST ACTION (the course change)

**Read `REFLECTION-2026-06-22.md` + `STATUS.md` ("Where it stands" + Outstanding §1–4).** Then:

**Attack M4 — the embedding `𝗣𝗔 ⊢ φ ⟹ Z_∞ ⊢^{α}_c {φ}`.** This is the highest-value target: the
**universal bottleneck** (required on every route to the headline) and untouched since lap-6 recon.

**Do NOT resume the witness-bounded cut-elim thread** (`cutReduceAllAux`, `Zekd`, any 4th index
calculus). The lap-8 findings + the cross-lap landscape memory both prove it is **off the critical
path** (single-index Hardy inequality is false; M5's witness-FREE cut-elim, done since lap 3, is what
the headline path uses, as-is). `wip/{BoundedZinfty,SplitZinfty,OperatorZinfty}.lean` are now
**reference only** — never the headline path.

### M4 — LAP-9 BUILT THE SCAFFOLD + PROVED `em` (`wip/Embedding.lean`, COMPILES)
`embed : Derivation2 (𝗣𝗔:Schema ℒₒᵣ) Γ → ∃ α c, ZinftyF.Provable α c Γ` over the **same**
`Finset (SyntacticFormula ℒₒᵣ)` substrate (no language translation). Verify: `lake env lean
wip/Embedding.lean` (only message = the expected `embed` `sorry` warning). Connection chain (verified):
`𝗣𝗔 ⊢ φ` —`provable_def`→ `(𝗣𝗔:Schema) ⊢ ↑φ` —`provable_iff_derivable2`→ `Nonempty (Derivation2
(𝗣𝗔:Schema) {↑φ})`.
- **`provable_em` FULLY PROVED, axiom-clean** (`[propext, choice, Quot.sound]`): the Z∞ excluded-middle
  `∀ φ Γ, φ∈Γ → ∼φ∈Γ → ∃ a, Provable a 0 Γ`, incl. the ∀/∃ numeral ω-family. **Promotable to
  `src/Zinfty.lean`.** Discharges the `closed` case.
- **`embed`: 6/10 cases DONE** (verum/and/or/wk/cut/closed).

**Next lap — the 4 remaining `embed` `sorry`s are the genuine deep content + are INTERDEPENDENT
(all need free-variable/substitution machinery for M5's `Deriv`). Build the shared enabler first:**
0. **(enabler) M5 renaming/substitution lemma** — the analogue of Foundation's `Derivation.rewrite`
   (`Calculus.lean:255`): `Provable α c Γ → Provable α c (Γ.image (Rew … ▹ ·))` by induction on `Deriv`
   (8 cases; the `allω` case needs care — rewriting must commute with the numeral family). Unlocks
   `shift`, `all`, `exs` together. **Do this first.**
1. **`shift`** — direct corollary of the enabler (`Rewriting.shift` is a `Rew`).
2. **`all`** — finitary ∀ (`free φ :: Γ.image shift`) → `allω`: substitute the free var `&0` by each
   numeral `nm n` (via the enabler / Foundation's `Derivation.rewrite`), embed each premise.
3. **`exs`** — witness term `t` → its numeral value (term-model: closed `ℒₒᵣ` terms denote numerals) →
   `Provable.exI`. Needs the free-variable framing settled by the enabler.
4. **`axm`** (the deepest) — `φ ∈ (𝗣𝗔:Schema)` = `↑σ`, `σ ∈ 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`.
   PeanoMinus = finite true ∀-sentences (finite ordinal); `univCl(succInd ψ)` derived via the ω-rule
   `Provable.allω` (`src/Zinfty.lean:183`). Buchholz §5.5 / Towsner §16.
**Fallback if M4 stalls → M7a** (parallel, shovel-ready): transparent `gAllReal = ∀x∃y[g_y(x)=0]`
(arithmetize `goodsteinSeq` via Foundation Σ₁ tools) + `𝗣𝗔 ⊢ goodsteinSentence ↔ gAllReal`, **gated by
`Bridge.lean`'s spec** so faithfulness can't regress.

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
