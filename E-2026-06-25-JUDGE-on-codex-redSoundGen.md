# Judge verdict — Codex's `redSoundGen` warning (2026-06-25)

**Ruling: Codex's warning has a TRUE core but is ~1 lap STALE, and its recommended remedy is
BACKWARD. Do NOT retreat to the ⊥-orbit target. The lap-96 `redSoundF` plan is correct — proceed.**

Context: Codex warned that `redSoundGen : ∀ d, ZDerivation d → ZDerivation (red d)` "encodes the
wrong theorem unless the reduct has been fully changed to carry `tpReduce` conclusions everywhere,"
and recommended retreating to `∀ d, ZDerivesEmpty d → ZDerivation (red d)`.

## What Codex got RIGHT
- A **keep-Π** `redSoundGen` is genuinely false: Buchholz 5.2.2 reduces the conclusion to
  `tp(dᵢ)(Π,0)` for a non-`Rep` selected premise, so a reduct that asserts `Π` is not a real
  `ZDerivation`. ✓ (This is the lap-90 finding the repo already documents.)
- "Don't keep proving through the keep-Π scaffold as if it were true." ✓ in spirit.

## Where Codex is STALE (kernel-verified against HEAD `f61e2c7`)
1. **The reduct ALREADY carries `tpReduce` conclusions.** Lap 96 (`b74f7a0`) landed the route-B
   conclusion-reducing `iRKr` IN-KERNEL: `iRKr` (`InternalZ.lean:5809`) emits
   `tpReduce (tp dᵢ) (fstIdx d) 0`; `fstIdx_iRKr` (`:6151`) proves it; `red_zK_rep`/`_rep_nonchain`
   restated to the reduced form; build green 1325, axiom-clean. Codex's premise "the old repo reduct
   kept Π" describes a PRE-lap-96 state. The migration Codex demands is already most of the way done.
2. **The `tp`-faithfulness subtlety is already handled.** The reduced conclusion reads the SELECTED
   premise's `tp dᵢ` (repo `tp` of a chain is always `Rep`, which would be wrong). Lap 96 removed the
   false `fstIdx_red_eq_tpReduce_of_Rep` over exactly this. `iRKr` reads `tp dᵢ`. ✓

## Why Codex's REMEDY (retreat to `ZDerivesEmpty d → ZDerivation (red d)`) is wrong
- **It does not sidestep the deep work.** `red` is a table recursion over ALL codes, and `redSound`
  is proved by structural induction whose IH must hold on the GENERAL sub-derivations of a ⊥-chain —
  its premises derive arbitrary sequents, not `∅→⊥`. A motive restricted to `ZDerivesEmpty d` gives a
  useless IH on those non-⊥ premises, so the induction will not close. You need a general
  (all-derivations) motive regardless of where you finally specialize.
- **The repo's `redSoundF` is the right general motive**:
  `redSoundF : ∀ d, ZDerivation d → ZDerivation (red d) ∧ fstIdx (red d) = redConcl d`
  — provable by plain structural induction (no orbit restriction), with the conclusion-TRACKING
  conjunct feeding `ZDerivation_red_zK_replace`'s `hredfst`/`hredtp`. You specialize to the ⊥-orbit
  only at the END (`fstIdx_red_of_emptyAnt_botSucc` + Cor 2.1, both already proved) to recover
  `ZDerivesEmpty` preservation. Retreating would throw away exactly the conclusion-tracking that makes
  the induction go through.

## The ONE actionable bit of Codex's warning (properly translated)
Don't burn the live grind re-proving the now-obsolete keep-Π piecemeal helpers — the OLD
`iCritAux`-target `ZDerivation_red_zK_replace` shape and the chain-replace `sorry` that tries to
discharge `tp dᵢ = Rep`. The lap-96 handoff already says "the piecemeal K-helpers are now obsolete;
the clean target is `redSoundF`." Codex's warning, de-staled, REINFORCES that — it does not justify
the ⊙-orbit retreat.

## Confidence + how this could be wrong
- Codex reads a pre-lap-96 picture: **~90%** (iRKr/fstIdx_iRKr kernel-verified, committed, build green
  per the `.githooks` gate — NOT host-reverified by the judge).
- Retreat fails to sidestep the deep work (table recursion needs a general motive): **~85%**.
- The splice branch (5.2.1) is the one soft spot where Codex's instinct could partially bite:
  `ZDerivation_red_zK_splice` was flagged "⚠ FALSE as stated" off the ⊥-orbit (junk halves for
  non-`Rep` dᵢ). BUT the lap-95 gate only routes to splice when dᵢ is a CRITICAL CHAIN, where
  `red dᵢ = iRcritG …` genuinely has the two halves and `tp dᵢ = Rep` holds automatically (chain ⟹
  Rep). So the gate plausibly rescues splice too — confirm when discharging `_splice`. **~70%.**
- The deepest residuals (`ZDerivation_red_zK_crit`, `_splice`) are the genuine Buchholz cut-elim
  content — TRUE in the math, multi-week to formalize. `redSoundF` being faithfully provable: **~75%.**

**Bottom line for the box: keep going on `redSoundF` (route-B, general motive, specialize at the end).
Ignore the suggestion to restrict to `ZDerivesEmpty`.**

---

## Follow-up: Codex's 4-step "feasible plan" (2026-06-25)
Codex now says (correctly) that the reduct derives the REDUCED sequent `tp(d)(Π,n)` and the old keep-Π
shape was false off `Rep` — "a transcription/architecture fidelity issue, not a deep math uncertainty."
This CONVERGES with route-B; Codex has effectively abandoned the ⊙-orbit-retreat remedy. Its 4 steps:

1. **Choose the source calculus (Coq PAω or Buchholz Z).** SETTLED, and a false choice. The calculus
   IS Buchholz Z, correctly — its `red`/`d[n]` operator is primitive-recursive on codes, which is what
   the Σ₁-over-codes route needs. Coq PAω (Bryce-Goré) is INFINITARY ω-rule cut-elim — the wrong source
   here (handoff: "do NOT port `cut_elim.v`"; a naive ω-node breaks `Fixpoint.StrongFinite`). Bryce-Goré
   is a FEASIBILITY witness + the C0.5 BRIDGE blueprint only, never the cut-elim method. Don't reopen.
   (NB: "keep grinding because Coq exists" is a strawman — the shape is Buchholz-Z-because-finitary.)
2. **Buchholz-Z ↔ Lean def-mapping table.** The genuinely additive idea — rank it HIGHER than Codex
   does. This is the [[designated-statement-audit-surface]] discipline applied to the reduction
   operator: one auditable table mapping `tpReduce`/`tp`/`iRK`/`iRKr`/`iRKs`/`iRKc`/`red`/`redConcl` →
   the exact Buchholz clause (Def 3.2 case 5.1/5.2.1/5.2.2; the `I(Π,n)` reductions §2 14.23/14.252;
   Thm 3.4 rank bound). Partial version already exists scattered in docstrings; consolidate it.
   ⚠️ **Only de-risks if each row is checked against the PDF, not transcribed from the Lean docstrings**
   (a self-referential table re-encodes any transcription error rather than catching it).
3. **Prove the reduced-sequent (source) statement first.** = `redSoundF`. Already the lap-96 plan. ✓
4. **Specialize to ∅→⊥ only after.** = the final ⊙-orbit specialization. ✓

Steps 3-4 are not optional process — they ARE the plan; proceed. Step 2 is a checkpoint deliverable
(or a judge/Trevor reading task, since it's audit-not-grind), NOT a blocker that pauses `redSoundF`.

**Why the kernel already guards most of this:** you cannot COMPLETE the general `redSoundF` with a wrong
off-orbit `tpReduce` — the induction passes through non-`Rep` chains, and `ZDerivation (red d)` there
requires the reduced conclusion to genuinely follow by the K-rule, so a wrong `tpReduce` gets you STUCK
(honest sorry), not a false green. The residual fidelity risk is concentrated in: `tpReduce_isymRep`
(true identity on `Rep` — small, checkable), Cor 2.1 (proved), `goodsteinSentence_faithful` (audited),
and whether `red`/`ZDerivation` faithfully encode Buchholz's calculus at all. That last one is what the
step-2 source-map (checked against the PDF) is for. **Confidence steps 1/3/4 are settled-correct: ~85%.
Step-2 source-map is worth doing: ~80%.**
