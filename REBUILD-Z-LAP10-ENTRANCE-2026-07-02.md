# REBUILD-Z — LAP-10 ENTRANCE ORDER: the α+γ restatement + pins 1–2 grind (architect, 2026-07-02) 🔒

> **Binding.** Written by the judge/architect pass that ruled on laps 8–9
> (`E-2026-07-02-JUDGE-rebuild-z-lap8-validation.md`). Ruling #1 resolved trap 9 PAPER-LITERAL:
> E–W Lemma 25's cut-reduction concludes at `α + β` — **no successor bump** — and Def 23's
> judgment gate stays fixed-base (`ewN α ≤ f 0`, unchanged). This lap executes the judged
> restatements, probes the seam, and — probe-gated — grinds pins 1–2. The statements below are
> RATIFIED by the ruling; believing one wrong = STOP and escalate with a kernel probe
> (self-ratification VOID).

## 1. The seam probe (R-0, wip-only, FIRST — gates everything below)

`wip/Lap10SeamProbe.lean`: kernel-check the restated pin-1's successor-case rebuild
(`γ = osucc β`, the exact case that forced the old bump):

- (i) **Strictness**: `β < γ → α + β < α + γ` and `0 < γ → α < α + γ` on ONote (route:
  `ONote.repr_add` + ordinal `add_lt_add_left`; NF hypotheses as the API demands).
- (ii) **Gate closure at the fresh root**: `ewN α ≤ g 0 → ewN γ ≤ f 0 → (∀ k, g 0 + k ≤ g k) →
  ewN (α + γ) ≤ g (f 0)` — the `ewN_add_le` + `noOsucc_closes` composition. Promote the
  base-additive lemma (`strictMono_base_add_le`-class) into `src/GoodsteinPA/EwIter.lean` as
  real content while at it.
- (iii) **Cut-read threading**: instance complexity — locate or prove
  `(φ/[nm n]).complexity = φ.complexity` (substitution preserves complexity), then
  `φ.complexity ≤ f 0 → f 0 ≤ g (f 0)` (g inflationary) closes the fresh `hcutRead`.

**T-L10**: any of (i)–(iii) kernel-fails → STOP, escalate with the probe file. Do NOT
improvise an alternative output ordinal (that is trap-9 territory; architect-owned).

## 2. Judged restatements (R-1..R-6; src, `OperatorZef2.lean` — NOT frozen)

- **(R-1) Pin 1 `cutReduceAllAuxRunning_Zf2`**: conclusion →
  `Zef2Prov (α + γ) e H (g ∘ f) c (Δ.erase (∃⁰ ∼φ) ∪ Γ)` (osucc DROPPED). Add hypotheses
  `hg_base : ∀ k, g 0 + k ≤ g k` and `hφRead : φ.complexity ≤ f 0`. Everything else verbatim.
  Docstring: supersedes the osucc form per ruling §3 (trap 9); cite Lemma 25.
- **(R-2) Pin 2 `stepAllω_Zf2`**: add `hg_base : ∀ k, g 0 + k ≤ g k` and
  `hχRead : χ.complexity ≤ f 0` (fed by `Zef2.cut`'s own `hcutRead` at the call site).
  Conclusion unchanged (existential `δ`).
- **(R-3) GRIND pins 1–2 — permitted THIS lap, gated on R-0 passing.** This is the P-d
  discharge, not the pass: re-thread the proven Zef skeletons (`OperatorZeh.lean:1523`/`:1752`)
  with the α+γ bookkeeping per the probe. The IH now returns UNBUMPED witnesses — premises land
  strictly below the fresh root by (i); gates close by (ii); fresh cut-reads by (iii). If a
  case kernel-obstructs → STOP, escalate with the localized probe (do not grind around it).
  ⚠️ Known latent seam, DOCUMENT-don't-decide: `rel1` is max-based and does not preserve
  base-additivity (E–W's `f[n]` is addition-based and does). The pins' top slots are never
  rel1-relativized so this lap is safe; note where the pass grind will meet it.
- **(R-4) Restate L-D `readoff_delta0_Zef2`** per ruling §4: conclusion
  `∃ n ≤ f 0, atomTrue (φ/[nm n])` (the repo's `atomTrue` — its def already evaluates arbitrary
  closed formulas); hypothesis = a REAL syntactic boundedness predicate on the instances
  (repo-native Δ₀/open-formula class; mini-probe the candidates, document the choice). The
  tautological `matrixTrue` form is VOID — delete it. Statement only; discharge stays rung D's
  own grind.
- **(R-5) Restate L-W** as the axiom's statement:
  `wainer_splice_Zef2 : (𝗣𝗔 ⊢ ↑goodsteinSentence) → ∃ o : ONote, o.NF ∧
  EventuallyLE GoodsteinPA.Dom.goodsteinLength (fun n => fastGrowing o n)` — theorem-with-sorry,
  homed where the imports allow (a new `WainerLadder.lean` leaf module importing
  `OperatorZef2` + `WainerRoute` is the sanctioned home; `OperatorZef2.lean` stays
  translation-free). Composition REAL where rung statements allow; `sorry` only at rung
  consumption. The trivially-dischargeable form is VOID — delete it.
- **(R-6) DELETE `embedding_Zef2`** (the placeholder is universally false — ruling §4). Leave a
  docstring TODO naming rung E's own statement lap: the W3 K-hypothesis re-base with
  `hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence`, concrete `Γ_G`, homed in `WainerLadder.lean` — and the
  MANDATED Ax2-adequacy pre-probe (`Zekd` has `trueRel`/`trueNrel`; `Zef2` has none; E–W Def 23
  has (Ax2)). Do NOT attempt rung E this lap.

## 3. Blueprint duties

`thm:zeh_rank_zero` → `\lean{}`-bind `rankToZero_Zef2`; `thm:wainer_splice` → bind the restated
`wainer_splice_Zef2`; `thm:zeh_embedding` stays decl-less noted until rung E's lap.
`lake exe blueprint_audit` MUST pass; reconciler rerun (`blueprint/annotate_depgraph.py --web`,
needs `~/.local/bin` on PATH).

## 4. Gates (every one, before the lap ends)

Build 🟢 · headline `peano_not_proves_goodstein` quadruple UNDRIFTED · `lean-sorry src/` delta
vs `HEAD` at fire time = pins 1–2 GONE if R-3 lands (else restated-and-disclosed), L-D/L-W
restated (still sorries), `embedding_Zef2` GONE, pass pin + old pin 3 + L-R unchanged · NO new
`axiom` · NO `native_decide` in src beyond the blessed base · wip evidence files untouched
(`Lap10SeamProbe.lean` is the only wip addition) · `blueprint_audit` passes · write
`REBUILD-Z-LAP10-VERDICT.md`; **STOP for the judge.**

## 5. FORBIDDEN

The pass body (`cutElimPass_Zef2`) and rung R/D discharge. Rung E in any form (its own lap).
`Zeh`/`Zef`/old-pin-3 statement tokens (docstring supersession notes only). Alternative output
ordinals beyond the ratified `α + γ` (nadd, osucc variants — dead). Touching the wip freeze
references. Self-ratification (VOID).

## 6. Treadmill shape (operator fires)

`--max-laps 2 --max-duration 6h` (or the codex-direct equivalent). Expected split: lap 1 =
R-0 probe + R-1/R-2/R-4/R-5/R-6 restatements (+ §3 blueprint); lap 2 = R-3 the pins grind.
Estimate: statements+probe 1 session (statement-lap cadence is 10-for-10); pins grind 1–3
sessions (the Zef proofs are the templates; the bookkeeping is new, the skeletons are not).
