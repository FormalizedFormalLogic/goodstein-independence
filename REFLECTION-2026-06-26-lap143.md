# DEEP REFLECTION — 2026-06-26 · lap 143

> Every-9th-lap altitude pass. Build re-verified 🟢 green (`lake build GoodsteinPA`, 1326 jobs).
> Headline footprint re-verified in-kernel (`lake env lean`):
> `peano_not_proves_goodstein = [propext, sorryAx, Classical.choice, Quot.sound]` — **0 math axioms**,
> lone `sorryAx` = crux-2 (the headline is a LOCKED literal `sorry`, anti-fraud).
> `peano_not_proves_goodstein_modulo_semantic = [propext, sorryAx, choice, Quot.sound, cmpStep…native_decide.ax_1_5]`
> (the worked variant; `sorryAx` = the open crux-2 chain; the `ax_*` is a 🟢 finite artifact).
> `goodsteinSentence_faithful` + `peano_not_proves_consistency` axiom-clean `[propext, choice, Quot.sound]`.
> Statement re-audited vs source — **no drift** (§4).

---

## TL;DR — the direction call

**Destination KEPT. The lap-132 existence-form pivot was the RIGHT call and stays. But laps 141-142
half-ABANDONED its core discipline, and the result is a 14-lap stall (128→142) in which the load-bearing
sorries on the live path have not dropped while genuine replacements pile up banked-but-unwired.**

The lap-132 pivot's whole point: the endgame returns a bare `∃ d'` (a sound, descending reduct EXISTS),
so it can be witnessed by ANY genuine reduct — you NEVER have to prove the fixed selector `red` is
faithful. The grind laps adopted the `∃`-shape structurally but **kept witnessing it with `red`**.
`descent_step_K_critical` (`Crux2Blueprint:1891`) — lap 141 — does
`⟨red (zK s r ds), ZDerivesEmptyR_red hd, …⟩`, and `ZDerivesEmptyR_red` routes soundness through
`redSoundGen` (:1471), which is FALSE/incomplete: its zInd case invokes the **kernel-FALSE**
`zKValidF_iIndReduct_of_zInd` (:80, refuted lap-136) and its zK case is an open sorry (:1508), and
`ZDerivation_red_zK` routes the critical case through the **kernel-FALSE** `ZDerivation_red_zK_crit`
(:1108, refuted lap-114). So the live `false_of_ZDerivesEmpty` path **transitively depends on two
lemmas already kernel-verified as false-as-stated** — sorries that can NEVER be discharged.

Meanwhile lap-142 proved the genuine red-free replacement `ZDerivation_iRKcCrit_critical_all` (:1847,
sorry-free, axiom-clean) — and left it **unwired**: `descent_step_K_critical` does not call it. Zero
false-dependence dropped. This is the textbook "bank a lemma, don't wire it" anti-pattern the operator's
success bar explicitly excludes.

**Highest-value next move: FINISH THE WIRING.** Only one support lemma is missing (`ZSeqAnt_iRKcCrit`).
Derive it, split `descent_step_K_critical` into ∀ (witness with `iRKcCrit`, dropping the false
:80/:1108 dependence for the dominant sub-case) and ¬ (a named honest `redexJ ≤ j0` residual), then do
the same to the Ind branch (witness with `iIndReductSeqG`, not `red d`). That is a substantive crux
advance — and exactly what M1b-term means.

---

## 1. Is the DESTINATION still right? — YES.

Kirby–Paris: `𝗣𝗔 ⊬ Goodstein`, via the resolved Route A (lap 45→46, unchanged):
`𝗣𝗔⊢γ →(crux-1, §3 all-primrec, DONE axiom-clean lap 57) 𝗣𝗔⊢PRWO(ε₀) →(crux-2, Gentzen ordinal
analysis) 𝗣𝗔⊢Con(𝗣𝗔)`, then Gödel II (`peano_not_proves_consistency`, axiom-clean). The headline and
faithfulness anchor are clean; the **entire** open math content reduces to the single girder crux-2
(the IΣ₁-internal cut-elimination / ε₀-descent termination). Nothing in mathlib is at this depth; the
proof is ~90 years old and fully written (Gentzen/Schütte/Takeuti; Buchholz §3 for the reduction
combinatorics). Feasibility is settled — the Gentzen Con(PA) core was machine-checked in Coq (Bryce–Goré
arXiv:2603.00487, Feb 2026). **No new information changes the endpoint.** The honest realistic state is
"one open girder (crux-2) + an axiom-clean remainder", with the girder a *proven theorem under
formalization* (disclosed `sorryAx`), classified 🟡 project-scale (NOT 🟠 generational, NOT 🔴 open).

## 2. Are we attacking the highest-value thing? — Right TARGET, wrong (regressed) METHOD.

The focus on crux-2's reduction engine is correct per hardest-first; crux-1 is done, the statement is
faithful, M2/M4 are lower-value plumbing. But read the trajectory lap-over-lap (git log; no treadmill
jsonl exists):

| lap | move | did a live-path sorry drop? |
|---|---|---|
| 128 | bank `ZDerivation_iRKcCrit_all` (∀-soundness) | no |
| 129 | diagnose red-STALL; "engine surgery required" | no |
| 132 | REFLECTION: pivot to existence-form (`redLeast`/`∃`) | (reflection) |
| 135 | settle existence-form = PIVOT; decompose `false_of_ZDerivesEmpty` | decomposed |
| 136 | Ind reduct false; build corrected `iIndReductSeqG` | no |
| 137 | REVIEW: type-correct PRWO seam; decompose (A)+(B) | decomposed |
| 138 | orbit (B0) PROVEN via `IIter` | (B0) closed |
| 139 | pair-parametric `_at` halves; refute μ-min (A) | no |
| 140 | REVIEW: "collapses to ONE lemma"; split by major-tag {3,4,5,6} | decomposed |
| 141 | abandon major-tag; critical/non-critical split; **witness critical with `red`** | no (REGRESSION) |
| 142 | bank `ZDerivation_iRKcCrit_critical_all` (∀, red-free) | no (UNWIRED) |

The diagnoses converge (good) and real assets get built (orbit, corrected Ind reduct, ∀-soundness both
forms). But the *load-bearing* sorries (`redSoundGen` :1471, `descent_step_K_noncritical` :1924,
`exists_sigma1_descending_step` :1992) have not dropped, and the critical case's false-dependence is
unchanged. This is fixation on a *formulation cadence* — decompose, bank, re-decompose — without the
final wiring step that makes a banked asset load-bear. The operator's bar ("a src sorry actually drops
on this path") is the right corrective and has been narrowly missed for laps.

## 3. What a sharp outside expert would say we're MISSING — the witnesses were never switched.

The existence-form pivot already did the *hard architectural* part of getting off `red`: it changed the
endgame's obligation from "`red` (a total Σ₁ function) is sound + descends on every orbit step" to "at
each ⊥-orbit point SOME sound descending reduct exists" (`ZDerivesEmptyR_descent_step : … → ∃ d', …`).
The grind laps treat "the engine swap" (re-keying `red`'s internal `permIdx`→`majorIdx` selection) as a
forbidden/atomic monolith — and it is. **But that monolith is not what the existence form needs.** It
needs only that each *branch* of `ZDerivesEmptyR_descent_step` *return* a genuine reduct as its `∃`
witness — a local, per-branch term substitution, no engine surgery, each branch independent. The banked
`iRKcCrit`/`iIndReductSeqG` soundness + descent lemmas are exactly those witnesses.

So the thing the grind laps can't see from inside the trees: **they are one `refine ⟨iRKcCrit …, …⟩`
away (per branch) from dropping the false-`red` dependence, and instead keep re-deriving soundness
lemmas they never plug in.** The fix is mechanical assembly, gated on a single missing support lemma
(`ZSeqAnt_iRKcCrit`).

Concretely, the live `false_of_ZDerivesEmpty` path's transitive sorries and their honest dispositions:

| sorry (Crux2Blueprint) | on live path via | disposition |
|---|---|---|
| `redSoundGen` :1471 (zK :1508 + zInd→false :80) | Ind & critical-K branches (`ZDerivesEmptyR_red`) | DEAD — drop by switching witnesses |
| `ZDerivation_red_zK_crit` :1108 (kernel-FALSE) | critical-K via `red` | DEAD — drop via `iRKcCrit` |
| `zKValidF_iIndReduct_of_zInd` :80 (kernel-FALSE) | Ind via `redSoundGen` | DEAD — drop via `iIndReductSeqG` |
| `ZDerivation_red_zK_splice` :1211, `_nonRep` :1384 | only the dead `red` chain | DEAD — off-path after switch |
| `descent_step_K_noncritical` :1924 | live (non-critical K) | GENUINE — Buchholz 5.2 (atomic reduct) |
| `exists_sigma1_descending_step` :1992 (A) | live (gDef packaging) | GENUINE — concrete `redStep`/witness-bound |
| ¬-case `redexJ ≤ j0` (after the split) | live (critical ¬) | GENUINE — pin `j0 = lh ds−1` on ⊥-orbit |

Once the witnesses switch, the four DEAD `red`-soundness sorries become provably off-path and are
legitimately relocatable to `wip/` (an abandoned route — NOT count-gaming, since nothing live references
them). The live sorry set then is the three GENUINE Buchholz/definability obligations — a clean,
fillable frontier.

## 4. Faithfulness at altitude — re-audited, no drift.

- Headline `peano_not_proves_goodstein` (`Statement.lean:22`): `𝗣𝗔 ⊬ ↑goodsteinSentence`, LOCKED literal
  `sorry`. In-kernel `[propext, sorryAx, choice, Quot.sound]` — 0 math axioms.
- `goodsteinSentence_faithful` (`Bridge.lean`): `(ℕ ⊧ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq m N = 0`
  — axiom-clean. The semantic anchor holds; `bump`/`goodsteinSeq` are the genuine hereditary-base bump.
- `peano_not_proves_consistency` (Gödel II hook): axiom-clean (`𝗣𝗔.Δ₁` discharged upstream, lap 89).
- The worked `peano_not_proves_goodstein_modulo_semantic`'s lone `sorryAx` traces to the open crux-2
  chain + `goodstein_implies_consistency` (the bare `sorry` awaiting crux-2). No `axiom` smuggling.

## Direction record

- **KEEP:** the destination + Route A; the existence-form pivot (lap-132); the banked per-reduct
  soundness (laps 112-119, 142) and descent lemmas (`iord_descent_iRKcCrit_corr`/`_neg`); the orbit (B0,
  lap-138); the corrected Ind reduct `iIndReductSeqG` (lap-136). Commit every green build; honest sorries.
- **STOP:** witnessing `ZDerivesEmptyR_descent_step` branches with `red` (the lap-141 regression);
  banking more iRKcCrit/Ind soundness lemmas without WIRING them into `descent_step_*`; attacking the
  false `red`-soundness sorries (:80, :1108, :1211, :1384, :1471) as stated; the major-premise-tag split;
  `zReg`/`zFresh`/`zSeqAnt` folds as a goal.
- **Single highest-value next target:** derive `ZSeqAnt_iRKcCrit`, then split `descent_step_K_critical`
  into ∀ (witness `iRKcCrit`, red-free) + ¬ (named `redexJ ≤ j0` sorry). This drops the dominant critical
  sub-case off the kernel-FALSE `red` soundness — a real crux advance, the operator's M1b-term bar.
  Next after that: re-witness the Ind branch with `iIndReductSeqG`; then attack ¬-case `redexJ ≤ j0`
  (pin `j0 = lh ds − 1` for ⊥-orbit chains) and (A) `exists_sigma1_descending_step` (concrete `redStep`).
