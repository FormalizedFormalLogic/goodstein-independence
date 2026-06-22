# HANDOFF — 2026-06-22 (lap 11)

> **Branch** `plan` · **HEAD** `bb0488e` (+docs after) · 5 commits this lap · build **green**
> (`lake build GoodsteinPA`, 1258 jobs) · headline `peano_not_proves_goodstein` = honest `sorry`
> (0 math axioms) · working tree clean.
> **Lap 11 COMPLETED M4 — the embedding `embedC` (axiom-clean, promoted to `src/`) — AND uncovered
> (via Towsner §13–17) that the headline needs the WITNESS-BOUNDED calculus `Zᵏ`: M5 drops the I∃
> bound `k`, so `embedC` is the *unbounded* embedding (reusable, but not the headline object). The
> `wip/Bounding.lean` bridge is FALSE as stated. See `ANALYSIS-2026-06-22-witness-bound-gap.md`.**

## 🎉 M4 — the embedding `embedC` — COMPLETE & axiom-clean (`src/GoodsteinPA/Embedding.lean`)
`embedC : Derivation2 (𝗣𝗔:Schema) Γ → ∃ c, ∀ e:ℕ→ℕ, ∃ α, Provable α c (Γ.image (asg e ▹))`.
`#print axioms embedC = [propext, Classical.choice, Quot.sound]` (no sorryAx, no math axioms). In
the default build (added to `src/GoodsteinPA.lean` root import). The two non-structural cases:
- **`exs`** (∃-intro, open witness `t`): `Provable.exI_closed` collapses the closed term `asg e ▹ t`
  to its numeral value via the **value-congruent EM** `provable_em_cong_gen` (arity-general; atomic
  leaves close by `axTrue` on value-equal arg vectors, quantifiers via `allω`/`exI` with the
  `subst_q_cons_app` substitution-composition identity) + one `cut`, then numeral-`exI`.
- **`axm`** (PA axiom `↑σ`): **ω-completeness** `provable_true` — every closed formula TRUE in ℕ is
  `Z∞`-derivable cut-free (induction on complexity). Since `ℕ ⊧ₘ* 𝗣𝗔`, every axiom is true. The
  ω-rule subsumes the Buchholz §5.5 meta-induction ENTIRELY — no induction-scheme special-casing.

Reusable axiom-clean assets now in `src/Embedding.lean`: `provable_em`, `provable_em_cong_gen/_cong`,
`Provable.exI_closed`, `provable_true`. (Superseded naive `embed`/`provable_rew` dropped on
promotion; history in `wip/Embedding.lean`.)

## 🎯 NEXT LAP — the WITNESS-BOUNDED calculus `Zᵏ` (read `ANALYSIS-2026-06-22-witness-bound-gap.md`)
⚠️ **Course-correction finding (lap 11, grounded in Towsner §13–17).** The lap-11 bridge scaffold
(`wip/Bounding.lean`, `cutfree_lt_eps0_absurd`) is **FALSE as stated**, and the lap-9 "bound directly
on the unbounded cut-free `Deriv`" reframe is **not viable**. Reason: Towsner's lower bound (Thm 17.1)
bites only via the **witness bound `k`** — the I∃ side condition `value(t) ≤ h_α(k)`. M5's
`Provable α c` tracks the cut rank `c` but DROPS `k` (the lap-4 finding). Without `k`, `provable_true`
gives a cut-free derivation of `{↑gs}` with ordinal `< ε₀` (bounded quantifiers cost `allω`=`ω`; `exI`
costs `+1` regardless of witness VALUE) — so the ordinal alone does not bite. ⟹ **`embedC` is the
*unbounded* embedding (Towsner Thm 14.2), subsumed by `provable_true`; it is correct + reusable but
NOT the headline object.**

**The corrected critical path (= lap-5 plan steps 1–4, now confirmed essential):**
1. **`Zᵏ`** — M5 `Deriv` + the `(α,k)` witness bound on `exI` (`value ≤ h_α k`). Revive the banked
   laps-6–8 `wip/` thread (`Zekd`/`OperatorZinfty`; lap-8 worked §19.2–19.5 + control axis). Cleanest
   carrier: a `Provable`-style wrapper `∃ α' ≤ α, α'.NF ∧ Zᵏ …` (lap-8 `ZekdProv` design).
2. **Bounded embedding (Towsner Thm 16.1/16.5/16.7)** into `Zᵏ`, ordinal `< ε₀`, finite cut rank.
   `axm`: universal axioms via **16.1** (`provable_true` on the quantifier-free matrix — bounded, no
   `∃`); induction via **16.5** bounded meta-induction (ordinal `ω·4#2^{rk}#2`), reusing `provable_em`
   + `Provable.exI_closed`. Structural cases: port `embedC`'s (and/or/cut/wk/shift/all) ~verbatim.
3. **`(α,k)`-cut-elim (Thm 19.9)** preserving the bound — the `wip/` Zekd §19 grind, now correctly
   motivated (`ANALYSIS-…-cutelim-k-threading.md` has the §19.6 plan + the `ZekdProv` wrapper design).
4. **Subformula bridge to `B`** (M6): a cut-free `Zᵏ` derivation of `{↑gs}` has only `↑gs`-subformulas
   = the `GForm` fragment, so it IS a `B`-derivation ⟹ contradiction with `lowerBound_hardy_selfcontained`.
   Plus the Σ₁-arithmetization seam (M7a: `codeOfREPred` matrix ↔ `atomTrue`) and the ONote↔Ordinal seam.

**BANKED reusable assets (all axiom-clean, `src/Embedding.lean`):** `provable_true` (→16.1),
`provable_em`/`provable_em_cong_gen`/`Provable.exI_closed` (→16.5/14.1), `embedC` structural cases,
M5 `cutElim` template. Do NOT discard — they are the building blocks of the bounded embedding.

## State of the spine (Route B)
- **M1, M2, Phase 0/1** — done, clean.
- **M4 embedding** (`src/Embedding.lean`, `embedC`) — **DONE this lap, axiom-clean, in the build.**
- **M5 ε₀ cut-elim** (`src/Zinfty.lean`, `Provable.cutElim`, `omegaTower_lt_epsilon0`) — done, clean.
- **M6 Hardy lower bound** (`src/LowerBound.lean`, `lowerBound_hardy_selfcontained`) — done, clean.
- **M7 bridge + assembly** (`wip/Bounding.lean`) — assembly SCAFFOLDED (proved mod B1 + bridge).

## Notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `sorry` intact.
- **Aristotle:** the `em_cong` job submitted this lap was CANCELLED (solved locally). Feed a bounded
  open lemma when one arises (e.g. a self-contained B1 ordinal-sup-`<ε₀` fact, or a B4 ONote bridge).
- **`WebFetch` dead; `WebSearch` works.** No open `ON-LINE-REQUEST.md`. For B2/B3 ground in `papers/`
  (Towsner; `papers/SOURCES.md`) — request via `ON-LINE-REQUEST.md` if a specific bound is missing.
- **Build:** `lake build GoodsteinPA` (1258); test wip via `lake env lean wip/Bounding.lean`.
- **Reference corpus** (`~/personal/claude/knowledge/.../lean-journey/reference/`): `grep -rl` first.

## Lap-11 commits
- `861d490` embedC exs PROVED (value-congruent EM ⟹ closed-term ∃-intro), 9/10.
- `86ed9ec` embedC axm PROVED via ω-completeness → M4 COMPLETE 10/10.
- `ff49e3b` promote embedC to `src/GoodsteinPA/Embedding.lean` (in the verified build).
- `bb0488e` Route-B assembly scaffold (`wip/Bounding.lean`) — gap isolated to B1 + bridge.
