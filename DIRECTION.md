# DIRECTION — GoodsteinPA (expedition charter)

Companion to `EXPEDITION-PLAN.md` (the math). This is the **operational charter** for an
autonomous treadmill campaign. Read both.

---

## ⚙️ CURRENT DIRECTIVE — altitude-lap-owned · binding on grind laps

> **WRITE-ACCESS: review & reflection (altitude) laps ONLY** (the operator may also set it). Grind
> laps READ this section and work strictly within it; they MUST NOT edit it. It **OUTRANKS** any
> `HANDOFF` "NEXT" pointer or in-flight campaign momentum — this is how an altitude lap's
> course-correction actually STICKS. The standing charter below changes rarely; THIS section turns
> over every few review laps. Keep it SHORT; detail lives in `PENDING_WORK.md` / `REFLECTION-*.md`.
> (Live milestone map = `E-CRUX2-ROADMAP-2026-06-24.md`; the phase list below is the standing charter.)

**Set: lap-140 (altitude review). Supersedes lap-137 — its two stale mandates are RETIRED: (1) the
orbit (B) it called "the load-bearing neglected piece" is DONE (lap 138, `exists_sigma1_iterate` via
`IIter`); (2) the `redLeast` μ-min route it mandated for (A) is REFUTED (lap 139, wrong-polarity
witness bound). The entire crux-2 termination now concentrates in ONE lemma — see below.**

- **THE objective (only this):** **M1b-term** = drive `descent_step_K_majorIdx` (`Crux2Blueprint:1764`)
  toward DISCHARGE. This single lemma is now the whole remaining termination wall, because:
  - The M3 contradiction `false_of_ZDerivesEmpty` is **SORRY-FREE** given `InternalPRWO V` (crux-1's
    deliverable, a hypothesis) + the bare-∃ per-step descent `ZDerivesEmptyR_descent_step`.
  - The orbit (B)/(B0) is **PROVEN** (lap 138).
  - (A) `exists_sigma1_descending_step` (the bare-∃ → total `𝚺₁` step packaging) **COLLAPSES INTO**
    `descent_step_K_majorIdx` via the *concrete* `redStep` route (lap-139 reconciliation): a concrete
    `𝚺₁` `redStep : V → V` gives `gDef` for free, and its descent clause IS `descent_step_K_majorIdx`.
    The μ-min packaging is refuted; do NOT re-attempt it. (A)'s shell (`redStep`/`redStepDef`) is
    tractable plumbing to bank only AFTER the descent content is in hand — hardest-first.
- **MANDATED next move:** **DECOMPOSE `descent_step_K_majorIdx` in `src/` into its three per-tag named
  sub-`sorry`s** (dispatch on the major-premise tag ∈ {3,4,5,6} via banked `majorIdx_botOrbit_reducible`):
  tag-3 (Ind) · tag-4 (chain) · tag-5/6 (∀/¬-axiom principal cut). RAISES src count = PROGRESS. Then
  **ASSEMBLE the most-banked sub-piece to a DROPPED src sorry** — the infra has been banked for two laps;
  the job now is to assemble, not bank more readouts. Hardest-first targets, in order:
  1. **tag-5/6**: assemble the explicit-pair `iCritReductG` soundness from the lap-139 pair-parametric
     `_at` halves (`haux0_at`/`haux1_at`/`_neg_at`) via `ZDerivation_iCritReductG_of` directly (NOT
     `iRcritG`, which bakes `redexI/redexJ`); thread the cut-rank drop. Genuine residual = the cutPartner
     `i'` is a PRINCIPAL R-intro of `∀p`/`¬..` (Buchholz criticality), not merely "some premise with that
     succedent". (lap-139 NEXT steps 1-3.)
  2. **tag-3 (Ind)**: assemble `isChainInf_iIndReductSeqG` via `isChainInf_of_last` (j0 = last index k),
     readouts already banked (`chainAsucc/chainAnt_iIndReductSeqG_*`). ⚠️ FIRST pin the exit-clause
     `t = t'+1`-vs-`numeral k` correspondence (lap-138 subtlety) or the exit sub-goal is mis-stated. Do
     NOT decompose tag-3 with the `red dⱼ` witness — that's the ordinal-shadow FALSE sorry (lap-138).
- **Success metric:** a `src/` sorry actually DROPS on this path (the operator's bar), OR honest
  `descent_step_K_majorIdx` per-tag decomposition into named `src/` sub-`sorry`s. NOT: off-path
  lemma-banking with no drop, count-management, or hiding an active sorry in `wip/`.
- **FORBIDDEN:** the `redLeast`/μ-min route for (A) (wrong polarity, refuted lap-139); re-keying
  `red`/`redexI`/`redexJ` to `majorIdx` (the engine swap, DIRECTION-forbidden — the pair-parametric
  `_at` layer is the correct alternative); more `zReg`/`zFresh`/`zSeqAnt` folds as a *goal*; the `red dⱼ`
  single-replace witness for tag-3 (false sorry); off-critical-path easy `sorry`s; M2 / M3 / M4 wiring.
- **Why:** lap 138 closed the orbit and lap 139 proved (A) reduces to `descent_step_K_majorIdx`, so the
  ENTIRE crux-2 termination is now this one lemma's three tag-cases. lap-137's directive still pointed at
  the built orbit and the refuted μ-route — obeying it wastes a lap. The operator's win condition (a src
  sorry drops) is met by decomposing this lemma finely and assembling a banked sub-piece, not by banking
  another readout layer.

### Directive history (newest first; append one line per altitude lap — never delete)
- **lap-140** (altitude review): RETIRED lap-137's two stale mandates (orbit (B) DONE lap-138; `redLeast` μ-route REFUTED lap-139). Crux-2 termination collapses to ONE lemma `descent_step_K_majorIdx`; (A) folds in via concrete `redStep`. MANDATE = decompose it into per-tag {3,4,5/6} src sub-`sorry`s + assemble a banked sub-piece to a DROP (tag-5/6 explicit-pair soundness, or tag-3 `isChainInf_iIndReductSeqG`).
- **lap-137** (altitude review): existence-form spike DONE; TYPE-CORRECTED the PRWO seam (`InternalPRWO` hyp; `→ False` in bare 𝗜𝚺₁ was Gödel-barred). PRIMARY = `exists_sigma1_descent_of_step` (the 𝚺₁ ε₀-descent — neglected through laps 135-136); secondary = `descent_step_K_majorIdx`. [stale: see lap-140]
- **pre-lap-135** (operator + judge): focus to **M1b-term only**; existence-form spike FIRST; success = a `src/` sorry drops.

---

## The goal (not a fixture — the destination) 🦸

**Prove `Statement.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence`** — Kirby–Paris (1982),
Peano Arithmetic does not prove Goodstein's theorem. That headline `sorry` is the *target*, not
a thing to preserve. The whole campaign exists to discharge it honestly.

## You (the box) own the full decomposition

This is **formalization of a known proof**, not origination. Gentzen's ordinal analysis is ~90
years old and in textbooks (Gentzen 1936, Schütte, Takeuti). Decomposing it into mathlib-shaped
Lean lemmas is exactly treadmill work. The phases (see `EXPEDITION-PLAN.md` for the math):

- **Phase 0 — encoding.** DONE except `goodsteinTerminates_re` (below). Milestone **M1**.
- **Phase 1 — Gödel II hook.** Surface `Con(𝗣𝗔)` + `𝗣𝗔 ⊬ Con(𝗣𝗔)` from Foundation's *existing*
  Gödel II (`FirstOrder/Incompleteness/Second.lean`), and reduce the headline to the single
  implication `𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`. Assembly. Milestone **M2**.
- **Phase 2 — the girder.** `TI(ε₀) ⊢ Con(𝗣𝗔)`: infinitary `PA_∞` (ω-rule), ordinal assignment
  `< ε₀` to derivations, ε₀-bounded cut-elimination. The deep core. Decompose it; build on
  mathlib's ε₀ (`SetTheory/Ordinal/Veblen`, `ONote`) + Foundation's finitary Hauptsatz. Milestones **M3…**.
- **Phase 3 — `Goodstein ⟹ TI(ε₀)`.** Re-express, syntactically, the ordinal descent that the
  termination Engine (`lean-formalizations` `Logic/Goodstein`) already does model-side.
- **Phase 4 — assemble.** `γ ⟹ TI(ε₀) ⟹ Con(𝗣𝗔)`, then Gödel II ⟹ `𝗣𝗔 ⊬ γ`. Discharge the
  Statement `sorry`. `#print axioms` clean.

Decompose with **disclosed sub-`sorry`s** — a named lemma held at `sorry` is honest, checkable
progress. Bank green laps; chip the girder lemma by lemma.

## Literature — on disk + offline requests 📚

**On hand (read these FIRST):** `papers/` holds pre-downloaded proof-theory references (PDFs;
gitignored, but present on your disk via the bind-mount). `papers/SOURCES.md` is the catalog —
what each paper is and which phase it serves (Gentzen ordinal analysis, PA_∞ cut-elimination,
Kirby–Paris, Goodstein/Cichoń, fast-growing hierarchy). **Ground the girder in these, not in
memory** — infinitary proof theory is exactly where an LLM confabulates a plausible-but-wrong
argument. Quote the source; don't reconstruct it.

**For gaps:** you are network-isolated (no web, no GitHub). When you need a reference that isn't
in `papers/` — a specific lemma statement, the exact ε₀ cut-elimination bound, a notation
convention — **do not guess and do not stall.** Write an **`ON-LINE-REQUEST.md`** at the repo root
with precise questions; a host fulfiller researches it and commits `ON-LINE-FINDINGS-*.md` (and
may add a PDF to `papers/`) for you to read next lap. Getting the math right from the literature
beats inventing a decomposition.

## M1 — the immediate residual

```
Encoding.goodsteinTerminates_re : REPred goodsteinTerminates
```
`goodsteinTerminates m := ∃ N, goodsteinSeq m N = 0` is r.e. (search `N`); the only non-trivial
input is **`Computable bump`** (`Defs.lean`, well-founded recursion on `Nat.log` — mathlib won't
auto-derive it). Route: `Computable bump` → `Computable₂ goodsteinSeq` → `ComputablePred (·=0)` →
`ComputablePred.to_re` → `REPred.projection` (∃ N). See Foundation `Vorspiel/Computability`. Pure
computability: zero faithfulness risk (typechecks or it doesn't). Closing M1 makes Phase 0
axiom-clean (`#print axioms goodsteinSentence_faithful` loses its `sorryAx`).

## ANTI-FRAUD guard (the one hard rule) 🚫

A `sorry`'d headline is honest; a **fake** one is the worst outcome. You may replace
`Statement.peano_not_proves_goodstein`'s `sorry` with a real proof **only if BOTH**:
1. `#print axioms peano_not_proves_goodstein` = `[propext, Classical.choice, Quot.sound]`
   (no `sorryAx`, no custom `axiom`), AND
2. it genuinely chains through built lemmas (no `native_decide` on the headline, no
   `axiom`-smuggling, no vacuous restatement).
If you cannot do both, **leave the `sorry`** and report the gap. The host audits
`#print axioms` on the headline every review lap. Inventing an axiom to "finish" = failure.

## LOCK — faithfulness anchors (do NOT edit) 🔒

Add lemmas freely, but never change these — they are the trust base that makes the headline mean
what it says:
- `Defs.lean` — audited `goodsteinSeq` / `bump` / `base`.
- `Bridge.lean`'s theorem **RHS** `∀ m, ∃ N, goodsteinSeq m N = 0`, and the proved bridge.
- `goodsteinTerminates`'s definition in `Encoding.lean`.

## Mode + execution

- **Expedition** (`--forever`): no self-stop; this is a long campaign measured in
  accumulated axiom-clean mathlib-shaped lemmas, not a single green.
- **Offline build prerequisite**: the box must `lake build GoodsteinPA` offline from the CoW'd
  Foundation v4.31 + mathlib oleans in `.lake/packages` + the box's v4.31.0 Linux toolchain.
  Never `lake update` / fetch. (If lap 1 can't build offline, that's the host's bug to fix —
  rebuild the box image / re-CoW — not yours to route around.)
