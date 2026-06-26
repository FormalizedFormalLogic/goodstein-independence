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

**Set: lap-143 (DEEP REFLECTION). Supersedes lap-140. Direction KEPT (existence-form pivot, lap-132);
the binding move is course-corrected because laps 141-142 half-ABANDONED the pivot's core discipline.**

- **THE objective (only this):** **M1b-term** = get the live `false_of_ZDerivesEmpty` path entirely
  OFF `red`'s false-as-stated soundness, by witnessing the existence-form `∃ d'` with GENUINE reducts.
  This is the lap-132 pivot's whole point — and it was REGRESSED:
  - `ZDerivesEmptyR_descent_step` (`Crux2Blueprint:1943`) returns a bare `∃ d'`, NOT `red d` — so it
    can witness with any sound, descending reduct. But TODAY both its load-bearing branches witness via
    `red`: the Ind branch (`⟨red d, ZDerivesEmptyR_red …⟩`, :1946) and `descent_step_K_critical`
    (`⟨red (zK …), ZDerivesEmptyR_red …⟩`, :1897). Both route soundness through `ZDerivesEmptyR_red` →
    **`redSoundGen` (:1471), which is FALSE/incomplete**: its zInd case invokes the kernel-FALSE
    `zKValidF_iIndReduct_of_zInd` (:80) and its zK case is an open sorry (:1508), and `ZDerivation_red_zK`
    routes critical soundness through the kernel-FALSE `ZDerivation_red_zK_crit` (:1108).
  - The GENUINE replacement is BANKED but UNWIRED: `ZDerivation_iRKcCrit_critical_all` (:1847, lap-142,
    sorry-free, axiom-clean — the critical ∀-case soundness with NO `red`), plus support
    `ZRegular_iRKcCrit_of_zK` / `ZFresh_iRKcCrit` / `fstIdx_iRKcCrit` / `iord_descent_iRKcCrit_corr`.
- **MANDATED next move (assemble, don't bank):**
  1. **Derive `ZSeqAnt_iRKcCrit`** (the ONE missing support lemma — `ZRegular`/`ZFresh`/`fstIdx`/descent
     all exist). Mirror `ZFresh_iRKcCrit` (`Zsubst.lean:3344`).
  2. **SPLIT `descent_step_K_critical` (:1891) into ∀ + ¬** on the R-redex shape (`hAcase`). Wire the
     **∀-case to `iRKcCrit`** as the witness — `⟨iRKcCrit (zK s r ds), ⟨ZDerivation_iRKcCrit_critical_all …,
     fstIdx_iRKcCrit▸…, ZRegular_iRKcCrit_of_zK …, ZFresh_iRKcCrit …, ZSeqAnt_iRKcCrit …⟩,
     iord_descent_iRKcCrit_corr …⟩` — dropping the dominant critical sub-case OFF `red`/`redSoundGen`/false
     :80/:1108. Leave the **¬-case as a NEW named sorry** `descent_step_K_critical_neg` (honest residual =
     `redexJ ≤ j0`, NOT free from `zKValid`). RAISES src count = PROGRESS (the ∀-case goes genuinely red-free).
  3. Then the same treatment for the **Ind branch** of `ZDerivesEmptyR_descent_step`: witness with the
     corrected-Ind reduct `iIndReductSeqG` (lap-136), not `red d`, dropping its `redSoundGen`/:80 dependence.
- **Success metric:** the live path's dependence on a FALSE `red`-soundness sorry DROPS for the critical
  ∀-case (the operator's bar — substantive even if the visible sorry count rises by the honest ¬-residual).
  NOT: banking another iRKcCrit/Ind lemma without wiring it into `descent_step_*`; count-management.
- **FORBIDDEN:** witnessing any `ZDerivesEmptyR_descent_step` branch with `red` (re-introduces the false
  soundness — this is the lap-141 regression); attacking `redSoundGen`(:1471)/`ZDerivation_red_zK_crit`(:1108)/
  `zKValidF_iIndReduct_of_zInd`(:80)/`ZDerivation_red_zK_splice`(:1211)/`_nonRep`(:1384) AS STATED (all
  FALSE/dead — they become off-path once the witnesses switch; relocate to `wip/` only AFTER the live path
  no longer references them, never before — premature relocation games the count); the `redLeast`/μ-min route
  for (A) (refuted lap-139); the major-premise-tag {3,4,5,6} split (abandoned lap-141); `zReg`/`zFresh`/`zSeqAnt`
  folds as a *goal*; off-critical-path easy `sorry`s; M2 / M4 wiring.
- **Why:** the existence form (`∃ d'`) was adopted precisely to free the path from proving `red`'s fixed
  selection faithful — but the witnesses were never switched, so the live path still pins to `red`'s
  false soundness and every lap banks genuine reducts that never load-bear. The crux advances ONLY when a
  genuine reduct actually becomes the witness. After the critical ∀-case + Ind branch are off `red`, the
  remaining honest sorries are {¬-case `redexJ≤j0`, non-critical 5.2 `descent_step_K_noncritical`, (A) `gDef`}
  — all genuine Buchholz cut-reduction / Foundation-definability content, none generational.

### Directive history (newest first; append one line per altitude lap — never delete)
- **lap-143** (DEEP REFLECTION): direction KEPT (existence-form pivot); FINDING = laps 141-142 regressed it — `descent_step_K_critical` re-witnesses with `red` (= the kernel-FALSE `redSoundGen`/:80/:1108 chain) and the genuine `ZDerivation_iRKcCrit_critical_all` (lap-142) is banked but UNWIRED. MANDATE = finish the pivot: derive `ZSeqAnt_iRKcCrit`, split `descent_step_K_critical` into ∀ (wire `iRKcCrit`, red-free) + ¬ (named `redexJ≤j0` sorry), then re-witness the Ind branch with `iIndReductSeqG`. FORBIDDEN = witnessing any descent branch with `red`. Retires lap-140's `descent_step_K_majorIdx`-by-major-tag mandate (abandoned lap-141).
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
