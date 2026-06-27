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

**Set: lap-152 (DEEP REFLECTION). Supersedes lap-149. Direction KEPT (existence-form pivot off `red` + the
lap-150 code-recursion frame). lap-149's mandate is DONE — tag-3 freshFlag DROPPED (lap 149); laps 150-151
landed the `genReduct_botSucc` code-recursion (Σ₁ structural induction), REFUTED the false single-premise
`seqUpdate` splice in-kernel, PROVED the FLATTEN engine `descent_step_K_spliceHalves`, and DROPPED the false
`descent_step_K_splice` via the `GenReductCert` (replace|flatten). The crux is now correctly isolated to the
GENERAL `Γ→⊥` reduction `genReduct_botSucc`, whose only open content is TWO master-key chain leaves.**

- **THE objective (only this):** **M1b-term** = close the live `false_of_ZDerivesEmpty` termination path.
  RE-VERIFIED axiom-clean (lap 152): headline `peano_not_proves_goodstein`, `goodsteinSentence_faithful`,
  `peano_not_proves_consistency` all axiom-clean / `[propext, sorryAx, choice, Quot.sound]` — ZERO custom
  math axioms, no drift. The whole crux-2 chain is reduced to **four disclosed live `sorryAx` leaves**, none
  needing `red`, none generational — and only TWO are independent:
  - **(MASTER KEY) `genReduct_chain_hasRedex` `Crux2Blueprint:2989`** — the chain's own §14.253 principal
    cut, returned as the FLATTEN `GenReductCert` (`Or.inr`). DESCENT IS FREE (`iord_descent_iRKcCrit_corr_of_redex`/`_neg_of_redex`); the halves are `iRKcCrit`'s `iCritReductSeq` components.
  - **(MASTER KEY) `genReduct_chain_noRedex` `Crux2Blueprint:3013`** — the genuine §14.254 recursion: reduce
    the major (tags 3/4) / Rep cut-partner (tags 5/6) by the per-premise **IH** (now hands back a
    `GenReductCert`), re-package as the parent's cert.
  - `descent_step_K_noncrit_axMajor` `:3226` (outer tag-5/6) and gDef `exists_sigma1_descending_step` `:3349`
    are NOT independent work: axMajor is the Γ=∅ special case of `genReduct_chain_noRedex`'s cut-partner
    branch (it falls out once the master keys + cut-partner identification land), and gDef needs the
    *constructive* reduct the genReduct cert already supplies. **Do NOT attack either standalone.**
- **MANDATED next move (lap-151's teed-up DROP, confirmed by this reflection): close `genReduct_chain_hasRedex`
  via the zSeqAnt tag-4 `Seq (seqAnt s)` FOLD.** Soundness of the principal-cut halves (`ZDerivation_iRKcCrit_all`/`_neg_botOrbit` + `ZRegular/ZFresh/ZSeqAnt_iRKcCrit`) needs `Seq (seqAnt s)`, which for a
  tag-4 CHAIN is NOT derivable from `ZSeqAnt` (the `zSeqAntNext` tag-4 branch flags `0`, `Zsubst:2003`). FIX =
  change that branch from `if zTag d = 4 then 0 else seqAntSeqFlag (fstIdx d)` to **always**
  `seqAntSeqFlag (fstIdx d)` — the EXACT shape of the proven lap-149 freshFlag fold / lap-146 zIndWff fold
  (both succeeded). Ripple (definability-dominated): (a) `zSeqAntNext` body `Zsubst:2003`; (b) `zSeqAntNextDef`
  σ-clause :2012 (drop the `t=4 ∧ fl=0` disjunct → always `fstIdx`+`seqAntSeqFlag`); (c) `zSeqAntNext_defined`
  simp :2021-2023; (d) `zSeqAnt_zK` :2164 (now carries the head flag) + `zSeqAnt_zK_premise_zero`; (e) the
  ~6 `ZSeqAnt_zK_*`/`_iRKcCrit` + `_of_seqInsert` + orbit-build sites that read the old tag-4=0 clause. Then
  `Seq (seqAnt s)` falls out of `hseqant` with NO threading, the halves' soundness closes, and
  `genReduct_chain_hasRedex` returns the FLATTEN cert sorry-free.
- **THEN — `genReduct_chain_noRedex` (the genuine recursion).** With the cert machinery validated end-to-end
  by hasRedex, prove the §14.254 recurse: `majorPrem_tag_mem` ⟹ major tag ∈{3,4,5,6}; reduce major (3/4) or
  identify+reduce the Rep cut-partner (5/6, via `majorPrem_zAxAll_cutPartner`/`_zAxNeg_cutPartner` — CHECK
  these exist/are sorry-free first) by the IH `GenReductCert`, then re-base the cert to the parent end-sequent.
  Closing both master keys makes `genReduct_botSucc` fully proven ⟹ the outer no-redex path (repMajor already
  sorry-free; axMajor mechanical) closes AND gDef gets its constructive reduct.
- **Success metric:** `genReduct_chain_hasRedex` sorry DROPS (a live-path src sorry, the operator's bar). NOT:
  banking support lemmas without the drop; relocating dead `red`-machinery for count-management; closing
  axMajor or gDef standalone (they are downstream).
- **FORBIDDEN:** witnessing any descent branch with `red`; the construction by `iord`-recursion
  (PRWO/Gödel-barred — CODE induction via `zDerivation_sigma_induction` ONLY); `redLeast`/μ-min for gDef
  (refuted lap-139); re-introducing the single-premise `seqUpdate`+combined-`iord` splice
  (`descent_step_K_splice`, refuted in-kernel lap 151 + judge-convergent — the faithful object is the FLATTEN
  `seqInsert` halves); attacking `descent_step_K_noncrit_axMajor` :3226 or gDef :3349 as STANDALONE leaves
  (re-derives the master-key combinatorics twice — they are corollaries); the zSeqAnt fold as a *goal* (it is
  mandated here ONLY because it directly unblocks `genReduct_chain_hasRedex`); the off-path dead `red`-soundness
  sorries {:82,:1257,:1367,:1563,:1653,:1765,:1868} AS STATED; M2 / M4 wiring.
- **Why:** `genReduct_chain_hasRedex` is the LAST teed-up tractable DROP and closing it validates the entire
  `GenReductCert` FLATTEN cert machinery end-to-end (exactly as `descent_step_Ind` validated the pivot at lap
  146) before the bigger `genReduct_chain_noRedex` recursion investment. The two master keys SUBSUME the outer
  no-redex path and feed gDef — closing them collapses three of the four open leaves, the highest-leverage
  move available. (Altitude note: M2 — the Foundation→Z bridge — is ~0% built and crux-entangled; "only the
  crux is left" must NOT read as "almost done." M1b-term first per hardest-first, but M2 is the next horizon.)

### Directive history (newest first; append one line per altitude lap — never delete)
- **lap-152** (DEEP REFLECTION): direction KEPT (existence-form pivot off `red` + lap-150 code-recursion frame). lap-149's mandate DONE (tag-3 freshFlag DROPPED lap 149); laps 150-151 landed `genReduct_botSucc` (Σ₁ code-recursion), REFUTED the false `seqUpdate` splice in-kernel, PROVED the FLATTEN engine `descent_step_K_spliceHalves`, DROPPED false `descent_step_K_splice` via `GenReductCert` (replace|flatten). RE-VERIFIED axiom-clean (headline/faithful/consistency all `[propext,(sorryAx,)choice,Quot.sound]`, 0 math axioms, no drift). FINDING = trajectory is HEALTHY (lap-143's banking-not-wiring/witness-with-red worries RESOLVED; steady crux DROPS 144→151, in-kernel refutation discipline alive); crux now correctly isolated to `genReduct_botSucc`. KEY ARCHITECTURAL INSIGHT = the four open leaves reduce to TWO master keys: `genReduct_chain_hasRedex` :2989 + `genReduct_chain_noRedex` :3013 SUBSUME the outer `descent_step_K_noncrit_axMajor` :3226 (Γ=∅ special case) and feed gDef :3349 (constructive reduct) — do NOT attack axMajor/gDef standalone. MANDATE = DROP `genReduct_chain_hasRedex` via the zSeqAnt tag-4 `Seq (seqAnt s)` fold (`zSeqAntNext` :2003, exact shape of the proven lap-149/146 folds), THEN `genReduct_chain_noRedex`. FORBIDDEN = `red`; `iord`-recursion for construction; `redLeast` for gDef; the refuted `seqUpdate` single-splice; axMajor/gDef standalone; the fold as a goal. ALTITUDE CAUTION = M2 (Foundation→Z bridge) ~0% built + crux-entangled — "only the crux left" ≠ "almost done."
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
