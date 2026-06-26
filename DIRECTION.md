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

**Set: lap-149 (FRESH-MIND REVIEW). Supersedes lap-146. Direction KEPT (existence-form pivot off `red`).
lap-146's mandate is DONE — `descent_step_Ind` DROPPED (lap 146); laps 147-148 correctly advanced into
Buchholz §5.2 noncritical, decomposing it faithfully per §14.254a/b (judge-C3). The binding move: take the
LAST tractable live leaf (tag-3 freshFlag), THEN turn to the genuine crux that has been deferred ~5 laps.**

- **THE objective (only this):** **M1b-term** = close the live `false_of_ZDerivesEmpty` termination path.
  VERIFIED axiom-clean (lap 149): `false_of_ZDerivesEmpty`, `ZDerivesEmptyR_descent_step`,
  `descent_step_K_noncrit_recurse` all `= [propext, sorryAx, Classical.choice, Quot.sound]` — ZERO custom
  math axioms; the whole crux-2 chain is reduced to **four disclosed live `sorryAx` leaves**, none needing
  `red`, none generational: (1) tag-3 freshFlag residual `Crux2Blueprint:2974`; (2) tag-4 K-recursion
  `descent_step_K_noncrit_repMajor_K`:2934; (3) tag-5/6 cut-partner `descent_step_K_noncrit_axMajor`:3002;
  (4) (A) `exists_sigma1_descending_step` gDef:3125. Leaves (2)+(3) ARE the genuine crux (the general
  `Γ→⊥` cut-reduction); (4) is the parallel Σ₁-definability crux; (1) is the last tractable leaf.
- **MANDATED next move (a real DROP — close tag-3 freshFlag, `Crux2Blueprint:2974`):** Strengthen
  `zFreshNext`'s tag-3 (`zInd`) branch (`Zsubst.lean:1673`) to carry the I∀-style eigenvariable freshness,
  mirroring the tag-1 clause :1671. Change the body from `max (znth s (zIndPrem0 d)) (znth s (zIndPrem1 d))`
  to `max (freshFlag (zIndEig d) (zIndP d) (seqAnt (fstIdx d))) (max (znth s (zIndPrem0 d)) (znth s
  (zIndPrem1 d)))` (`zIndEig (zInd …)=π₁ at'`, `zIndP (zInd …)=p`, both confirmed). This is a **FOCUSED,
  definability-dominated ripple** (the EXACT shape of the lap-146 `zIndWff` strengthening that dropped
  `descent_step_Ind`; `zFresh` is C-free so `zphi_*` untouched): edit (a) `zFreshNext` body :1673;
  (b) `zFreshNextDef` σ-clause :1683-1684 (mirror the tag-1 σ-block :1679-1681 — add `freshFlagDef` +
  `zIndEigDef` + `zIndPDef` + `seqAntDef∘fstIdxDef`); (c) `zFreshNext_defined` simp set :1691-1694 (add
  `zIndEig_defined`/`zIndP_defined`; `freshFlag_defined`/`fstIdx`/`seqAnt` already present); (d) `zFresh_zInd`
  simp :1812 (new `max freshFlag (max …)`); (e) `zFresh_zsubst` tag-3 case :1947-1955 — mirror the tag-1
  case :1935-1941 (`freshFlag_zsubst_eq_zero` + `seqAnt_fvSubstSeqt`); add the trivial extractor
  `freshFlag_eq_zero_of_zfresh_zInd` (mirror :1872); (f) re-project the 4 max-extraction sites that read
  `ZFresh d0/d1` off `zFresh_zInd` (`Crux2Blueprint:2657/2660/2801/2804`, +`Zsubst:2894`) through the new
  outer `max`. Then at :2974 the residual `freshFlag (π₁ at'') p' (seqAnt s')=0` falls directly from
  `hfreshm : ZFresh (znth ds majorIdx)` (= `zFresh (zInd …)=0` now carries it; `le`-project + `fstIdx_zInd`).
  **tag-3 repMajor goes fully sorry-free** → `descent_step_K_noncrit_repMajor` drops its `htag3` branch.
- **THEN — the CRUX (do NOT hunt more leaves; this is what's left):** with freshFlag closed, the only live
  crux-2 sorries are the **general `Γ→⊥` cut-reduction by strong induction on derivation CODE** (leaves 2934
  + 3002; Buchholz Thm 2.1 / §14.253-254 — NOT `iord`-recursion, PRWO/Gödel-barred) and **gDef** (3125).
  START the general reduction: decompose it into the code-induction skeleton (a `ZDerivation`-valued
  same-end-sequent descending `Rep`-reduct of a structurally-smaller premise, recursion on the finite code,
  not the ordinal), re-reading §14.253-254 in `scratchpad/buchholz-gentzen.txt`. A disclosed sub-`sorry`
  decomposition of THIS is a successful crux lap even with nothing closed.
- **Success metric:** tag-3 freshFlag sorry DROPS (a live-path src sorry, the operator's bar). NOT: banking
  support lemmas without the drop; relocating dead `red`-machinery for count-management.
- **FORBIDDEN:** witnessing any `ZDerivesEmptyR_descent_step` branch with `red`; the general step by
  `iord`-recursion (PRWO/Gödel-barred — structural/code induction ONLY); the `redLeast`/μ-min route for (A)
  gDef (refuted lap-139); collapsing the repMajor/axMajor §14.254a/b split (judge-C2/C3 endorsed); attacking
  the off-path dead `red`-soundness sorries {:82,:1257,:1367,:1563,:1653,:1765,:1868} AS STATED (relocate to
  `wip/` only as a DELIBERATE cleanup AFTER freshFlag drops, never count-management); jumping to gDef / the
  general recursion BEFORE freshFlag drops (it is teed-up and validates the no-redex machinery end-to-end);
  `zReg`/`zFresh`/`zSeqAnt` folds as a *goal* (the tag-3 fold is mandated here ONLY because it directly drops
  :2974 — not as engine-work); off-critical-path easy `sorry`s; M2 / M4 wiring.
- **Why:** freshFlag is the LAST teed-up tractable DROP; closing it validates the entire no-redex repMajor
  machinery (`descent_step_K_replace` + `ind_reduct_botSucc_of_fresh`) end-to-end, exactly as
  `descent_step_Ind` validated the pivot at lap 146 — de-risking before the big recursion investment. After
  it, the residual is PURELY the two genuine cruxes (general code-recursion + gDef), now isolated and
  unavoidable, which is the correct setup to attack them head-on instead of deferring to ever-smaller leaves.

### Directive history (newest first; append one line per altitude lap — never delete)
- **lap-149** (FRESH-MIND REVIEW): direction KEPT (existence-form pivot off `red`); lap-146's mandate is DONE (`descent_step_Ind` DROPPED lap 146; laps 147-148 advanced §5.2 noncritical, decomposed faithfully per Buchholz §14.254a/b). VERIFIED axiom-clean: `false_of_ZDerivesEmpty`/`ZDerivesEmptyR_descent_step`/`descent_step_K_noncrit_recurse` all `[propext, sorryAx, choice, Quot.sound]` — 0 math axioms; crux-2 = 4 disclosed `sorryAx` leaves {tag-3 freshFlag :2974, tag-4 K-recursion :2934, axMajor 5/6 :3002, gDef :3125}. FINDING = crux-neglect signal forming — recent laps closed surrounding machinery (Ind reducts, replace plumbing, dispatchers) while the genuine crux (general `Γ→⊥` cut-reduction by code-induction, leaves 2934+3002) stays untouched; tag-3 freshFlag is the LAST tractable leaf. MANDATE = DROP tag-3 freshFlag via the focused `zFreshNext` tag-3→freshFlag strengthening (mirror tag-1 I∀ :1671, exact shape of the proven lap-146 `zIndWff` ripple), THEN turn to the crux (general code-recursion + gDef) — NO more leaf-hunting. FORBIDDEN = `red` witnesses; `iord`-recursion for the general step; `redLeast` for gDef; jumping to the crux before freshFlag drops.
- **lap-146** (FRESH-MIND REVIEW): direction KEPT; lap-143's mandate is DONE (live path FULLY off `red`, lap-144; `ZDerivesEmptyR_descent_step` sorry-free). FINDING = the live termination path now has exactly THREE co-equal genuine sorries {`descent_step_Ind`, `descent_step_K_noncritical` §5.2, (A) `gDef`}, none generational. VERIFIED lap-145's `zIndWff` diagnosis is REAL not stale (step clause :1684 is membership `inAnt(F(a))`, base clause :1682 is an equation — genuine asymmetry) AND that the strengthening is REQUIRED for soundness (membership-only admits unsound Ind nodes) + more faithful to Buchholz; the ZSeqAnt + "no-cascade-docstring" reframes both CHECKED and refuted. MANDATE = DROP `descent_step_Ind` via the focused, definability-dominated `zIndWff` step-clause→shape ripple (`seqAnt(fstIdx prem1) = seqCons (seqAnt(fstIdx d)) (F(a))`); descent + `p=⊥` already banked. FORBIDDEN = `red` witnesses; the refuted reframes; jumping to §5.2/(A) before Ind drops.
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

- **Phase 0 — encoding.** ✅ DONE - Milestone **M1** complete (`goodsteinTerminates_re` + `computable_bump` proven, 0 sorries; verified 2026-06-26).
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

## M1 — ✅ DONE (do NOT re-attack)

`Encoding.goodsteinTerminates_re : REPred goodsteinTerminates` is **PROVEN** (verified 2026-06-26:
0 sorries in `Encoding.lean` / `Computability.lean` / `Defs.lean`). It landed as built:
`computable_bump : Computable₂ bump` (`Computability.lean:131`) → `goodsteinTerminates_re`
(`Encoding.lean:60`). Effect realized: **Phase 0 is axiom-clean** - `goodsteinSentence_faithful`
(`Bridge.lean:34`) prints `[propext, Classical.choice, Quot.sound]`, no `sorryAx` (re-verified
in-kernel lap 132). Nothing here to do.

> Historical route (for reference): `Computable bump` (well-founded recursion on `Nat.log`) →
> `Computable₂ goodsteinSeq` → `ComputablePred (·=0)` → `ComputablePred.to_re` →
> `REPred.projection` (∃ N), per Foundation `Vorspiel/Computability`.

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
