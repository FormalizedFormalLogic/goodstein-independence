# REBUILD-Z — SERIES-1 ORDER: the batched grind pipeline (architect, 2026-07-02) 🔒

> **Binding. Supersedes `REBUILD-Z-LAP10-ENTRANCE-2026-07-02.md` as the firing unit** (its
> R-items live on verbatim as Stage 1 here). Operator-directed cadence change: judge passes
> have ~fixed cost per review, so grind stages CHAIN IN SERIES under one fire and the judge
> reviews the pipeline once at the end. The safety invariant is unchanged and is what makes
> this batchable: **every statement below is pre-ratified by
> `E-2026-07-02-JUDGE-rebuild-z-lap8-validation.md` and given as VERBATIM Lean text — copy it,
> never compose it.** A stage that believes a ratified statement is wrong HALTS ITS LANE with a
> localized kernel probe and moves to the other lane. Self-ratification VOID. Rung E is
> untouchable (its own judged statement lap — the Ax2-adequacy probe forks the design).

## 0. Run ledger (the pipeline-status artifact)

Maintain `REBUILD-Z-SERIES-1-LEDGER.md`: one block per stage — status
(LANDED/ESCALATED/SKIPPED), commits, gates run, escalation probes if any. Append-only; commit
per stage. This file is what the judge reads first; keep it honest and terse.

## Lane P (the pass runway): Stages 1P → 2 → 3 → 4, strictly in order

### Stage 1 — statements + seam probe (the ONLY statement-touching stage; all pre-ratified)

- **(R-0) `wip/Lap10SeamProbe.lean`** — kernel-check the α+γ successor-case seam:
  (i) `β < γ → α + β < α + γ` and `0 < γ → α < α + γ` on ONote (`ONote.repr_add` +
  `Ordinal.add_lt_add_left`; NF as the API demands);
  (ii) `ewN α ≤ g 0 → ewN γ ≤ f 0 → (∀ k, g 0 + k ≤ g k) → ewN (α + γ) ≤ g (f 0)`
  (`ewN_add_le` + the `noOsucc_closes` pattern — promote the base-additive lemma to
  `src/GoodsteinPA/EwIter.lean` as real content);
  (iii) instance complexity: locate or prove `(φ/[nm n]).complexity = φ.complexity`, then
  `φ.complexity ≤ f 0 → f 0 ≤ g (f 0)` closes the fresh `hcutRead`.
  **T-S1**: any kernel failure → halt lane P (lane D proceeds), escalate with the probe. Do
  NOT improvise alternative output ordinals.
- **(R-1) Pin 1 restated VERBATIM** (docstring: supersedes the osucc form per ruling §3, trap 9,
  E–W Lemma 25; body `sorry` until Stage 2):

  ```lean
  theorem cutReduceAllAuxRunning_Zf2 {φ : SyntacticSemiformula ℒₒᵣ 1} {c : ℕ} {α e : ONote}
      {Γ : Seq} {g : ℕ → ℕ} (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
      (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x) (hg_base : ∀ k, g 0 + k ≤ g k)
      (fam : ∀ n (H' : ONote → Prop), Zef2 α e H' (rel1 g n) c (insert (φ/[nm n]) Γ)) :
      ∀ {γ : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Δ : Seq}, Zef2 γ e H f c Δ → γ.NF →
        Monotone f → (∀ x, x ≤ f x) → φ.complexity ≤ f 0 → (∃⁰ ∼φ) ∈ Δ →
        Zef2Prov (α + γ) e H (g ∘ f) c (Δ.erase (∃⁰ ∼φ) ∪ Γ)
  ```

  (`hg_base` implies `hg_infl`; both kept for template continuity with the Zef proof.)
- **(R-2) Pin 2 restated VERBATIM** (body `sorry` until Stage 2):

  ```lean
  theorem stepAllω_Zf2 {E : ONote} {H : ONote → Prop} {c : ℕ} {Γ : Seq}
      {χ : SyntacticSemiformula ℒₒᵣ 1} {βφ βψ : ONote} {f g : ℕ → ℕ}
      (hENF : E.NF) (hχc : χ.complexity < c)
      (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x) (hg_base : ∀ k, g 0 + k ≤ g k)
      (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x) (hχRead : χ.complexity ≤ f 0)
      (D₁ : Zef2Prov (expTower βφ) E H g c (insert (∀⁰ χ) Γ))
      (D₂ : Zef2Prov (expTower βψ) E H f c (insert (∃⁰ ∼χ) Γ)) :
      ∃ δ : ONote, δ.NF ∧ Cl H δ ∧ Zef2Prov δ E H (g ∘ f) c Γ
  ```
- **(R-4) L-D restated** — delete the `matrixTrue` form; new statement:

  ```lean
  theorem readoff_delta0_Zef2 {φ : SyntacticSemiformula ℒₒᵣ 1}
      (hφbdd : ∀ n, <BoundedInstance> (φ/[nm n]))
      {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
      (dd : Zef2 α e H f 0 {(∃⁰ φ)}) :
      ∃ n ≤ f 0, atomTrue (φ/[nm n])
  ```

  `<BoundedInstance>` is the ONE delegated choice in this series: the repo-native syntactic
  Δ₀/bounded-formula predicate. Mini-probe ≥2 candidates in wip, COMMIT the probe + a
  docstring justification BEFORE any Stage-5 grind consumes it (the judge audits the choice
  post-hoc; a wrong choice wastes only lane D).
- **(R-5) L-W restated** — delete the trivially-dischargeable form; new file
  `src/GoodsteinPA/WainerLadder.lean` (imports `OperatorZef2` + `WainerRoute`; wire into the
  blueprint root + `mk_all`):

  ```lean
  theorem wainer_splice_Zef2 :
      (𝗣𝗔 ⊢ ↑goodsteinSentence) →
        ∃ o : ONote, o.NF ∧
          EventuallyLE GoodsteinPA.Dom.goodsteinLength (fun n => fastGrowing o n)
  ```

  (The axiom's literal statement as the discharge vehicle; body `sorry`, composition becomes
  real as rungs land. Docstring: rung W, consumes E/R/D + the Hardy Lemma-19 brackets.)
- **(R-6) DELETE `embedding_Zef2`** (universally false placeholder — ruling §4). Docstring TODO
  in `WainerLadder.lean` naming rung E's own statement lap + the MANDATED Ax2-adequacy probe.
- **Blueprint**: `thm:zeh_rank_zero` → `\lean{rankToZero_Zef2}`; `thm:wainer_splice` →
  `\lean{wainer_splice_Zef2}`; `thm:zeh_embedding` stays decl-less noted. `blueprint_audit`
  must pass; reconciler rerun.

### Stage 2 — pins 1–2 grind (gate: R-0 passed)

Re-thread the proven Zef skeletons (`OperatorZeh.lean:1523`/`:1752`) over `Zef2` with the α+γ
bookkeeping: the IH now returns UNBUMPED witnesses — premises land strictly below the fresh
root by R-0(i); node gates close by R-0(ii); fresh cut-reads by R-0(iii). A kernel obstruction
in a case → localized probe, halt lane P, escalate. (This is the P-d discharge; est. 1–2 laps.)

### Stage 3 — THE PASS grind (gate: Stage 2 landed) — UNLOCKED by this order

`cutElimPass_Zef2` (statement ratified lap 7, verbatim in src — do not touch it): E–W Lemma
27/30's single predicative rank step; the ordinal collapses (`collapse α`), the slot iterates
(`ewIter f α`). Templates: the Zef pin-3 landscape + the lap-7 P3 engine `ewIter_rel1_le`
(the allω reassembly containment) + E–W Lemma 30's proof structure (PDF pp. 12–14).
⚠️ **Known seam, pre-analyzed (ruling §3)**: E–W's relativization `f[n](m) = f(n+m)` preserves
(f.1); the repo's `rel1 f n = f (max n ·)` does NOT preserve strictness/base-additivity. The
recursion at ω-nodes must therefore thread **Monotone+infl-only invariants** (the lap-7 P1
lift already proved these suffice for the lift; `ewIter_monotone`/`ewIter_infl` are the
pattern) rather than demanding `EwF1` of relativized slots. If a step is kernel-blocked
WITHOUT `EwF1`-of-`rel1`-slots → that is a statement-level wall: localized probe, halt lane P,
escalate (a `rel1` redesign is a judged calculus amendment — NOT yours). Est. 2–4 laps; this
is the concentrated-risk girder — an honest early escalation here is a GOOD series outcome.

### Stage 4 — rung R grind (gate: Stage 3 landed)

`rankToZero_Zef2`: plain induction over the pass down the cut rank (`collapseIter`/
`ewIterTower` are in place, NF lemma proven). Est. 1 lap.

## Lane D (independent; run when lane P halts/waits, or after Stage 4)

### Stage 5 — rung D grind (gate: R-4 landed + its predicate probe committed)

Discharge `readoff_delta0_Zef2` (Towsner §5.4 pattern): extend the proven Zef read-off
extraction (its axL true-side case-split is the template, `OperatorZeh.lean:1801`ff) from
atomic to bounded matrices. Consumes NOTHING from lane P. Est. 2–3 laps.

## Gates (per stage, cheap; full sweep at series end)

Build 🟢 · headline `peano_not_proves_goodstein` quadruple UNDRIFTED · restated statements
DIFF-IDENTICAL to the verbatim text above (whitespace/name-resolution aside) · `lean-sorry src/`
delta = exactly the disclosed pins in play · NO new `axiom` · NO `native_decide` in src beyond
the blessed base · wip freeze references untouched · `blueprint_audit` passes · ledger updated
+ committed per stage. Series end: `REBUILD-Z-SERIES-1-VERDICT.md` (roll-up of the ledger) —
**STOP for the judge.**

## FORBIDDEN

Rung E in any form (incl. "just stating it"). Statement text beyond the verbatim blocks above
(the `<BoundedInstance>` slot is the sole delegated choice). `Zeh`/`Zef`/old-pin-3 tokens
(docstring supersession notes only). `rel1`/`Zef2`-constructor redesigns (judged amendments).
Alternative output ordinals beyond the ratified `α + γ`. Touching wip freeze references.
Self-ratification (VOID).

## Fire shape (operator)

One fire: `--max-laps 10 --max-duration 24h` (or an equivalent codex series). Expected value
even in the escalation-heavy branch: Stage 1 + pins + a sharp pass-seam probe + lane D — a
full judge-pass worth of pipeline either way. Estimates: S1 = 1 lap · S2 = 1–2 · S3 = 2–4 ·
S4 = 1 · S5 = 2–3 (grind estimates historically run 2–4× optimistic; the lap caps bound it).
