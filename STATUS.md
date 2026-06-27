# STATUS — GoodsteinPA 📊

**`𝗣𝗔 ⊬ Goodstein` (Kirby–Paris), axiom-free — single open girder = crux-2 (IΣ₁-internal Gentzen consistency).**
· **Build**: 🟢 green (1326 jobs) · **Updated**: lap 164 (**FRESH-MIND REVIEW**; HEAD `09cd161`) · 2026-06-27 ·
Direction KEPT (lap-161 still current). **Lap-163 DISCHARGED escape (i) ⊥-exit ex-falso in-kernel** — `zAxBot`
(tag-8 ⊥-left leaf, the ZPhi 9th disjunct) + the `exFalsoClose` cert, axiom-clean (`zDerivation_zAxBot` =
`[propext, choice, Quot.sound]`, no `sorryAx`). The {3,4}-producer cut-reduction core (Buchholz Thm 2.1) was
CLOSED laps 159-160 (`repProducerClose`, consumed at `Crux2Blueprint:3578-3581`). **The `residual` (:3475) now
holds ONLY two families: (ii) C-exit R-intro replay (tag-1/2 major producing `C`) + (iii) tag-5/6 thread-escape
(shared with `axMajorResidual`).** NEXT = decompose `residual` into named src sub-`sorry`s (`cExitReplay`/
`threadEscapeClose`), then close (ii) via the major premise's own R-intro reduct spliced same-end-sequent.
Closing `residual` cascades → drops `genReduct_chain_noRedex_anySucc` → `axMajorResidual` +
`descent_step_K_noncrit_axMajor`. See `DIRECTION.md` CURRENT DIRECTIVE (lap-164 banner), `HANDOFF-2026-06-27-lap163.md`.
· Headline `peano_not_proves_goodstein = [propext, sorryAx, Classical.choice, Quot.sound]` (**0 math axioms**, bare-sorry
headline); `goodsteinSentence_faithful` + `peano_not_proves_consistency` axiom-clean; `false_of_ZDerivesEmpty` =
`[propext, sorryAx, choice, Quot.sound]` (0 math axioms) (real `#print axioms`, lap 164, no drift). **ALTITUDE:** a
sorry-free `false_of_ZDerivesEmpty` is NOT the headline — `goodstein_implies_consistency` (`Reduction.lean:68`) is a
bare sorry, NOT YET wired to it; the M2/M4 embedding bridge is ~0% built (the dominant remaining feasibility
unknown). "Only the crux left" ≠ "almost done." The lap that closes `false_of_ZDerivesEmpty` HANDS to altitude to re-plan M2.

> **🧭 Lap-164 — FRESH-MIND REVIEW. Direction KEPT; ex-falso (i) now CLOSED. Read FIRST — current.**
> Build re-verified 🟢 green (1326, exit 0); real `#print axioms` in-kernel: headline `peano_not_proves_goodstein` +
> `false_of_ZDerivesEmpty` = `[propext, sorryAx, choice, Quot.sound]` (**0 math axioms**); `peano_not_proves_consistency` +
> `goodsteinSentence_faithful` = `[propext, choice, Quot.sound]` (clean) — no drift. **THE CALL:** lap-161's mandate
> (build the internal ex-falso/weakening lemma FIRST) is DONE — lap-163 closed escape (i) ⊥-exit ex-falso via the `zAxBot`
> tag-8 ⊥-left leaf (the ZPhi 9th disjunct) + the `exFalsoClose` cert, axiom-clean (`zDerivation_zAxBot` has NO `sorryAx`).
> The `residual` (`Crux2Blueprint:3475`) now holds ONLY two families: **(ii) C-exit R-intro replay** (tag-1/2 major produces
> the conclusion succedent `C`; dispatch lands at :3613/:3619) and **(iii) tag-5/6 thread-escape** (:3631/:3646 + the
> `tryProducerClose`/`closeZAxNeg` residual landings, shared with `axMajorResidual`). **CRUX-NEGLECT CHECK:** laps 161-163
> all hit the directive's named piece (not side-leaves) — not fixation; but `false_of_ZDerivesEmpty` is the cut-elim ENGINE,
> still UNWIRED to the headline's bare sorry — M2 remains the dominant feasibility unknown, deferred by design until the
> engine closes. **MANDATE (`DIRECTION.md` lap-164 banner):** decompose `residual` into named src sub-`sorry`s
> (`cExitReplay` / `threadEscapeClose`), then close (ii) via the major premise's OWN R-intro reduct spliced same-end-sequent
> (it is already a `zIall`/`zIneg` deriving `Γⱼ→C`; `õ`-drops as a strict sub-derivation), (iii) via a shared
> `threadEscapeClose` reused by `axMajorResidual`. Closing `residual` cascades to drop `genReduct_chain_noRedex_anySucc` →
> `axMajorResidual` + `descent_step_K_noncrit_axMajor` (4 of 6 sorries); gDef (:4378) separable. FORBIDDEN/engines per
> lap-161. **ALTITUDE CAUTION (binding):** the lap that closes `false_of_ZDerivesEmpty` HANDS to an altitude lap to re-plan
> the M2 bridge. See `DIRECTION.md` CURRENT DIRECTIVE (lap-164), `HANDOFF-2026-06-27-lap163.md`.

> **🧘 Lap-161 — DEEP REFLECTION (every-9th, prev altitude lap-158). Directive RE-SYNCED. Read FIRST — current.**
> Build re-verified 🟢 green (1326, exit 0); real `#print axioms` in-kernel: headline `peano_not_proves_goodstein` =
> `[propext, sorryAx, choice, Quot.sound]` (**0 math axioms**, bare-sorry headline), `peano_not_proves_consistency` +
> `goodsteinSentence_faithful` = `[propext, choice, Quot.sound]` (clean), `false_of_ZDerivesEmpty` =
> `[propext, sorryAx, choice, Quot.sound]` (0 math axioms) — no drift. **THE CALL:** the lap-158 directive is STALE +
> internally contradictory — its review half mandated an "outer degree-induction design spike FIRST," but its OWN spike
> (`9ac1bf3`) REFUTED that hypothesis: the {3,4} producer closes by the EXISTING **code-induction** with LOCAL per-flatten
> degree headroom (premise's own `irk+1 ≤ idg(premise)`), NO global degree-induction. **Laps 159-160 then WIRED + CLOSED
> the {3,4}-producer core in-kernel** — `repProducerClose` (`Crux2Blueprint:3455`) `:= Or.inl (certReplace_of_premise_cert
> … (IH m …))`, non-sorried, consumed in the live dispatch at `:3578-3581`. So "the irreducible heart of crux-2" the old
> directive names as open is **CRACKED**. The open `residual` (:3451) / `axMajorResidual` (:3735) now hold ONLY the
> **STRUCTURAL escape set**: (i) ⊥-exit ex-falso (`⊥∈Γ`/`^∀⊥∈Γ ⟹ Γ→C`, no single Z-rule — needs internal ⊥-elim/weakening,
> the ONE new piece), (ii) C-exit R-intro replay, (iii) tag-5/6 thread-escape (shared between the two residuals). **VERDICT:**
> progress GENUINE (residual content shrank monotonically 148→160; the {3,4} core actually closed), but laps 155-160 added
> 3 anySucc leaves WITHOUT dropping a whole-lemma src sorry — next laps must DROP. **MANDATE (`DIRECTION.md` lap-161):**
> build the internal EX-FALSO/WEAKENING lemma FIRST (standalone, mirror `leafCloseC`/`axNegCloseGen` cert shape at
> :3462/:3473), wire it + R-intro replay + a factored shared `threadEscapeClose` to CLOSE `residual` (:3451) → drops the
> noRedex_anySucc leaf → (with the 2 other anySucc leaves) thin-wraps `genReduct_botSucc` → DROPS `axMajorResidual` (:3735)
> AND `descent_step_K_noncrit_axMajor` (:4180, Γ=∅ twin, same content) = FOUR of six sorries. gDef (:4309) separable
> (witness-bound/constructive reduct, NOT μ-min). FORBIDDEN = re-spiking the {3,4} producer / outer degree-induction (DONE +
> refuted); `red`; `iord`-recursion; `redLeast`; the refuted `seqUpdate` splice; axMajor/gDef standalone before the port;
> off-path dead red-soundness sorries; **M2/M3/M4 wiring**. **ALTITUDE CAUTION (sharpened, binding):** a sorry-free
> `false_of_ZDerivesEmpty` is NOT the headline — `goodstein_implies_consistency` (`Reduction.lean:68`) is a BARE sorry, NOT
> YET wired to `false_of_ZDerivesEmpty` (the M2/M4 embedding PA-proof→`ZDerivesEmptyR` is ~0% built); girder #1 (γ→PRWO) is
> partly built. "0 math axioms / only the crux left" ≠ "almost done." The lap that closes `false_of_ZDerivesEmpty` hands to
> an altitude lap to re-plan the M2 bridge. See `REFLECTION-2026-06-27-lap161.md`, `DIRECTION.md` CURRENT DIRECTIVE (lap-161),
> `HANDOFF-2026-06-27-lap160.md`.

> **🧭 Lap-155 — FRESH-MIND REVIEW. Direction KEPT; tag-5/6 COURSE-CORRECTED off lap-136. (historical — see lap-161.)**
> Build re-verified 🟢 green (1326); in-kernel: headline `peano_not_proves_goodstein = [propext, sorryAx,
> choice, Quot.sound]` (**0 math axioms**), `goodsteinSentence_faithful` + `peano_not_proves_consistency` +
> `false_of_ZDerivesEmpty` re-audited — no drift. **The call:** lap-152's mandate is DONE (MASTER KEY #1
> `genReduct_chain_hasRedex` DROPPED lap 153; #2 `genReduct_chain_noRedex` 6/8 branches PROVEN lap 154); the
> whole M1b-term termination crux is now the SINGLE open leaf **`axMajorClose`** (`Crux2Blueprint:3418`), the
> tag-5/6 L-axiom cut-partner. **COURSE-CORRECTION:** the lap-154 handoff frames its hard sub-case (b) as the
> lap-136 general-succedent induction reduct (`⟨d0,d1[a:=0..k-1]⟩`, `k=⟦t⟧` — the repo's hardest target,
> kernel-refuted at face value). The review judges that PESSIMISTIC + PREMATURE. Kernel-grounded insight: the
> tag-5 major `zAxAll s' p' k'` has `p'=⊥` (⊥-exit + `zAxAllSuccWff` + `eq_falsum_of_substs1_falsum`), so the
> cut formula is `^∀⊥`; its active formula threads via the chain's `hthread` to **`^∀⊥ ∈ Γ` (a)** ∨ **earlier
> premise `i'` concluding `^∀⊥` (b)**. Under `hnolow` (no redex below j0) a **direct R-intro `zIall` of `^∀⊥`
> below j0 is IMPOSSIBLE** — it would be an `isRedexPair` with jstar (VERIFIED `isRedexPair:4820` fires on
> `(zIall ^∀p, zAxAll ^∀p)`: i-end right-symbol, j-end left-symbol, same cut formula). So `^∀⊥` is never
> *created* below j0 — it only threads from Γ, collapsing (b)→(a). **MANDATE (`DIRECTION.md` lap-155):** the
> SUCCEDENT-THREADING COLLAPSE — (1) 2 reusable ordinal lemmas `w<ω^w` + summand-≤-fold [teed-up first DROP];
> (2) sub-case (a) `axLeafClose` (fresh `zAxAll s ⊥ k'` derives `Γ→⊥`, õ-dropping) + generalize
> `majorPrem_*_cutPartner` off `seqAnt s=∅`; (3) collapse (b): leaf→`chainAsucc_threaded_of_leaf`,
> R-intro→`hnolow`, zK→recurse, residual = at most a `zInd` concluding `^∀⊥` (check it's even derivable).
> FORBIDDEN = building the lap-136 reduct before the collapse is tested to exhaustion; `red`; `iord`-recursion;
> `redLeast`; the refuted `seqUpdate` splice; `axMajor`/`gDef` standalone. ALTITUDE CAUTION (still binding): M2
> (Foundation→Z bridge) ~0% built — "only the crux is left" ≠ "almost done." See `HANDOFF-2026-06-27-lap155.md`,
> `DIRECTION.md` CURRENT DIRECTIVE (lap-155), `PENDING_WORK.md` (lap-155 top).

> **🔑 Lap-153 — MASTER KEY #1 DROPPED. Read FIRST — current.** Build re-verified 🟢 green (1326);
> `genReduct_chain_hasRedex` (`Crux2Blueprint:3048`) sorry → **PROVEN**, `#print axioms`-clean
> `[propext, choice, Quot.sound]` (no `sorryAx`); new shared helper `certFlatten_of_critHalves` likewise clean;
> `false_of_ZDerivesEmpty` trace unchanged `[propext, sorryAx, choice, Quot.sound]` (0 math axioms). The §14.253
> principal cut realized at the GENERAL `Γ→⊥` level (Γ nonempty) off `red`, returning the FLATTEN
> `GenReductCert` (`Or.inr`). **KEY INSIGHT:** the two FLATTEN halves are the `iCritReductSeq` premises of the
> proven `iRKcCrit` reduct — extracted by premise-INVERSION (not rebuilt); the N2 per-half `õ`/`idg` drops fall
> out of `iotil_zK`/`idg_zK` being `fstIdx`-irrelevant + `iotil_zK_lt_replace`/`idg_zK_le_replace` from the N1
> records; `Seq (seqAnt s)` from the lap-152 fold's `seq_seqAnt_zK`. This **VALIDATES the entire `GenReductCert`
> FLATTEN machinery end-to-end** (the cert consumer `descent_step_K_noncrit_repMajor` →
> `descent_step_K_spliceHalves` was already banked). **NEXT = MASTER KEY #2 `genReduct_chain_noRedex`
> (`:3294`)**, the genuine §14.254 recursion via the per-premise IH cert. Closing it collapses the downstream
> `axMajor` (`:3507`) + gDef (`:3630`). See `HANDOFF-2026-06-27-lap153.md`, `DIRECTION.md` (lap-152, still
> binding). ALTITUDE CAUTION (lap-152) STILL HOLDS: M2 (Foundation→Z bridge) ~0% built — "crux only" ≠ "almost done."

> **🧘 Lap-152 — DEEP REFLECTION (every-9th, prev lap-143). Direction KEPT; crux isolated to TWO master keys; read FIRST — current.**
> Re-verified 🟢 green (1326); re-ran `#print axioms` in-kernel: headline `peano_not_proves_goodstein =
> [propext, sorryAx, choice, Quot.sound]` (**0 math axioms**), `goodsteinSentence_faithful` +
> `peano_not_proves_consistency` = `[propext, choice, Quot.sound]` (axiom-clean). Statement re-audited vs
> source — **no drift**. **The call:** trajectory since lap-143 is HEALTHY — the lap-143 worries
> (banking-not-wiring, witnessing with `red`) are RESOLVED; laps 144→151 are genuine steady crux DROPS (live
> path off `red` 144; `descent_step_Ind` 146; §5.2 has-redex 147; tag-3 freshFlag 149; **code-recursion frame
> `genReduct_botSucc` 150**; **in-kernel refutation of the `seqUpdate` splice + FLATTEN engine
> `descent_step_K_spliceHalves` PROVEN + false `descent_step_K_splice` DELETED 151**). **KEY ARCHITECTURAL
> INSIGHT:** the four open live leaves reduce to **TWO master keys** — `genReduct_chain_hasRedex`
> (`Crux2Blueprint:2989`, §14.253 principal cut, descent FREE) + `genReduct_chain_noRedex` (`:3013`, §14.254
> recursion via IH) — which **SUBSUME** the outer `descent_step_K_noncrit_axMajor` (`:3226`, the `Γ=∅` special
> case of the cut-partner reduction) and **feed** `gDef` (`:3349`, which needs the *constructive* reduct the
> `GenReductCert` already supplies). So do NOT attack `axMajor`/`gDef` standalone — closing the two master keys
> collapses three of the four leaves. **MANDATE (`DIRECTION.md` lap-152):** DROP `genReduct_chain_hasRedex` via
> the zSeqAnt tag-4 `Seq (seqAnt s)` fold (`zSeqAntNext` `Zsubst:2003` → always `seqAntSeqFlag (fstIdx d)`; the
> EXACT shape of the proven lap-149 freshFlag / lap-146 zIndWff folds), THEN `genReduct_chain_noRedex`.
> FORBIDDEN = `red`; `iord`-recursion for construction; `redLeast` for gDef; the refuted `seqUpdate`
> single-splice; `axMajor`/`gDef` standalone; the fold as a goal. **ALTITUDE CAUTION:** M2 (Foundation→Z
> bridge) is ~0% built + crux-entangled — "only the crux is left" must NOT read as "almost done." See
> `REFLECTION-2026-06-27-lap152.md`, `DIRECTION.md` CURRENT DIRECTIVE (lap-152), `HANDOFF-2026-06-27-lap151.md`.

> **🧭 Lap-149 — FRESH-MIND REVIEW. Direction KEPT (existence-form pivot off `red`); read FIRST — current.**
> Re-verified 🟢 green (1326); re-ran `#print axioms` in-kernel: `false_of_ZDerivesEmpty` (M3),
> `ZDerivesEmptyR_descent_step` (E'), `descent_step_K_noncrit_recurse` (§5.2 no-redex dispatcher), and the
> headline ALL `= [propext, sorryAx, Classical.choice, Quot.sound]` — **0 custom math axioms**; the entire
> crux-2 chain is reduced to **four disclosed `sorryAx` leaves**: (1) tag-3 freshFlag residual
> `Crux2Blueprint:2974`; (2) tag-4 K-recursion `descent_step_K_noncrit_repMajor_K`:2934; (3) tag-5/6 cut-partner
> `descent_step_K_noncrit_axMajor`:3002; (4) (A) gDef `exists_sigma1_descending_step`:3125. **The call:**
> lap-146's mandate is DONE (`descent_step_Ind` DROPPED lap 146; laps 147-148 advanced §5.2 noncritical,
> decomposed faithfully per Buchholz §14.254a/b). FINDING = a crux-neglect signal is forming — laps 144-148
> closed the *surrounding* machinery (Ind reducts, `descent_step_K_replace` plumbing, dispatchers) while the
> genuine deepest crux — the **general `Γ→⊥` cut-reduction by strong induction on derivation CODE** (leaves
> 2934+3002) — stays untouched; tag-3 freshFlag is the LAST tractable leaf. **✅ DROPPED THIS LAP:** executed
> the mandate — strengthened `zFreshNext`'s tag-3 branch to carry `freshFlag (zIndEig d) ⊥ (seqAnt (fstIdx d))`
> (a **dummy `^⊥` matrix** — `ind_reduct_botSucc_of_fresh` consumes only the antecedent part, and the real
> `IsSemiformula 1` matrix would force a level-1 yak-shave; the ⊥-orbit conclusion is `⊥` so antecedent-only
> freshness is the complete eigenvariable condition). tag-3 freshFlag sorry GONE;
> `descent_step_K_noncrit_repMajor` tag-3 branch sorry-free; `ind_reduct_botSucc_of_fresh`/`zFresh_zsubst`
> axiom-clean `[propext, choice, Quot.sound]`; headline unchanged 0 math axioms. Crux-2 now = **3 disclosed
> sorryAx leaves** {tag-4 K-recursion :2938, axMajor 5/6 :3012, gDef :3135}. **NEXT (DIRECTION.md lap-149):**
> the general `Γ→⊥` code-recursion crux (leaves 2938+3012) + gDef — NO more leaf-hunting. FORBIDDEN = `red`;
> `iord`-recursion for the general step; `redLeast` for gDef. See `DIRECTION.md` CURRENT DIRECTIVE (lap-149),
> `HANDOFF-2026-06-26-lap149.md`, `PENDING_WORK.md`.

> **🧭 Lap-148 — §14.254 REPLACE plumbing banked + no-redex residual re-split (judge-C3 aligned); read FIRST — current.**
> Build re-verified 🟢 green (1326); headline `[propext, sorryAx, Classical.choice, Quot.sound]` (0 math
> axioms) — no drift. Acted on the host-flagged judge review (`E-2026-06-26-JUDGE-codex-review.md` **C3**,
> converged with Codex): prove the two no-redex cases SEPARATELY + a shared replace tool; do NOT write
> `descent_step_general` blind. **Source-grounded the no-redex dichotomy in Buchholz §14.25** (major premise
> never endform — GENERAL `Γⱼ⊆Θ`+`Aⱼ≈⊥` argument; no-redex = §14.254a/b, BOTH "replace a `Rep` premise with its
> same-end-sequent reduct" — the judge-C3 shared-motive gate SATISFIED). **CORRECTION:** no-redex `axMajor` is
> §14.254b (reduce the Rep cut-partner), NOT §14.253 (the principal cut = the has-redex case, already proven).
> **Banked `descent_step_K_replace`** (`Crux2Blueprint:2475`, axiom-clean) — the shared §14.254 replace step
> (off `red`, off criticality): any premise with a same-end-sequent descending regular/fresh/seqAnt
> `ZDerivation` reduct yields a strictly-descending `ZDerivesEmptyR` (pure assembly over banked
> `ZDerivation_iCritAux_of` + `iord_descent_iCritAux_of_ZDerivation` + the `_of_seqUpdate` invariants).
> **Re-split `descent_step_K_noncrit_recurse`** (lap-147 had collapsed it to one sorry with a docstring wrongly
> claiming "all replace the major premise") into the faithful §14.254a/b leaves, restoring the judge-C2
> three-leaf M1b path `{repMajor:2527, axMajor:2545, gDef:2913}`. No sorry DROPPED — both leaves bottom out in
> the GENERAL `Γ→⊥` reduction (strong induction on CODE, Buchholz Thm 2.1; the surrounding replace plumbing is
> now discharged). NEXT (hardest-first): generalize `descent_step_Ind` off `Γ=∅` → tag-3 repMajor DROPS via
> `descent_step_K_replace`. See `HANDOFF-2026-06-26-lap148.md`, `PENDING_WORK.md` lap-148.

> **🎉🧭 Lap-147 — §5.2 has-redex half PROVEN (criticality DECOUPLED); residual = the general `Γ→⊥` recursion (historical).**
> Build re-verified 🟢 green (1326); headline `[propext, sorryAx, Classical.choice, Quot.sound]` (0 math
> axioms) — no drift. Operator SOLE-OBJECTIVE = M1b-term (terminate crux-2). Attacked the hardest-first live
> sorry `descent_step_K_noncritical` (Buchholz §5.2) and got it off `red` AND off CRITICALITY. **Key in-kernel
> finding:** the `iRKcCrit` critical-cut reduct's soundness/descent/invariants are ALL criticality-free GIVEN
> the redex — criticality entered ONLY at `isRedexPair_redexCode_of_zKValid` (to prove a redex exists). Landed
> the decoupling lemmas (`isRedexPair_redexCode_of_exists`, `redexI_lt_of_redexPair`,
> `redZKReady_of_zKValidF_exists`, `iord_descent_iRKcCrit_corr_of_redex`/`_neg_of_redex`) and assembled
> **`descent_step_K_hasRedex`** (`Crux2Blueprint:2346`): a regular `∅→⊥` chain with the `isChainInf` exit data +
> ANY in-region redex pair has the genuine `iRKcCrit` reduct as a strictly-`iord`-descending `ZDerivesEmptyR`,
> NO `red`/criticality. `descent_step_K_noncritical` is now a sorry-FREE has-redex/no-redex dispatcher: redex
> below the exit → `hasRedex` (**PROVEN** — Buchholz §14.253 principal cut, now covering NON-critical chains
> too); no such redex → `descent_step_K_noncrit_recurse` (the LONE §5.2 residual). **The has-redex half DROPS.**
> The residual = REDUCE the (Rep/chain-partnered) major premise = the GENERAL `Γ→⊥` Z-derivation reduction
> (Buchholz Thm 2.1 / Cor 2.1), closure via `descent_step_general` by STRUCTURAL induction (NOT `iord` — that
> is PRWO/Gödel-barred). See `HANDOFF-2026-06-26-lap147.md`, `PENDING_WORK.md` lap-147.

> **🎉🧭 Lap-146 REVIEW + GRIND — `descent_step_Ind` DROPPED (axiom-clean, off `red`); live termination path down to TWO genuine sorries (read FIRST — current).**
> After the fresh-mind review (below) validated lap-145's direction, this lap EXECUTED it end-to-end: landed the
> `zIndWff` membership→shape strengthening (`a2b2a3a`, closing a latent soundness gap), then ASSEMBLED and
> **DROPPED `descent_step_Ind`** (`59b339b`, `#print axioms = [propext, Classical.choice, Quot.sound]`) — the
> Ind-root soundness/descent, mirroring `descent_step_K_critical_all`, enabled by the strengthening + a NEW
> axiom-clean `zKValidF_leafconds_of_ZDerivation` (InternalZ). The live `false_of_ZDerivesEmpty` path now has
> just TWO sorries: `descent_step_K_noncritical` (:2139, Buchholz §5.2 atomic reduction) + (A) `gDef` (:2457).
> Headline `[propext, sorryAx, Classical.choice, Quot.sound]` (0 math axioms) — no drift. See
> `HANDOFF-2026-06-26-lap146.md`, `PENDING_WORK.md` lap-146.

> **🧭 Lap-146 FRESH-MIND REVIEW — direction KEPT + SHARPENED; the live termination path is FULLY off `red`, down to THREE co-equal genuine sorries.**
> Re-verified 🟢 green (1326); headline `[propext, sorryAx, Classical.choice, Quot.sound]` (0 math axioms) — no
> drift. **The call:** lap-143's mandate is DONE (lap-144 wired the live path off `red`; `ZDerivesEmptyR_descent_step`
> :2270 is sorry-free, dispatching Ind→`descent_step_Ind` / K→`descent_step_K_majorIdx`, NO kernel-FALSE soundness).
> The `false_of_ZDerivesEmpty` path now has exactly **three live sorries: `descent_step_Ind` (:2262),
> `descent_step_K_noncritical` (:2139, Buchholz §5.2 atomic reduct), (A) `exists_sigma1_descending_step` (:2327,
> the `gDef` Σ₁-Semisentence)** — all genuine Buchholz cut-reduction / Foundation-definability, none generational.
> **Validated lap-145's diagnosis IN-KERNEL (not a stale-obstruction repeat):** `zIndWff`'s step clause (:1684) is
> MEMBERSHIP `inAnt(F(a))` while its base clause (:1682) is an EQUATION — a real asymmetry; and the strengthening is
> **REQUIRED for soundness** (membership-only admits *unsound* Ind nodes: a lax `d1 ⊢ {⊥,X}→⊥` leaks stray `X` past
> the rule) + more faithful to Buchholz, not a hack. **Refuted two cheaper reframes:** `ZSeqAnt` only flags
> sequence-wellformedness (not antecedent content), and the zIndWff "strengthen-body-without-the-ZPhi-cascade"
> docstring is over-optimistic (`zIndWff` IS in the `zPhi` Ind disjunct, InternalZ:5399/5451). **MANDATE (DIRECTION.md
> lap-146):** DROP `descent_step_Ind` via the FOCUSED, definability-dominated `zIndWff` step-clause→shape ripple
> (`seqAnt(fstIdx prem1) = seqCons (seqAnt(fstIdx d)) (F(a))`; `seqConsDef`/`seqAddAntDef` already available,
> `sas=seqAnt(fstIdx d)` already bound); descent (`iord_descent_iIndReductSeqG_one`) + `p=⊥`
> (`eq_falsum_of_substs1_falsum`) already banked ⟹ the strengthening is the whole remaining content. NOT a 64-site
> cascade (`zIndWff` is C-free → `zphi_monotone`/`_strong_finite` untouched). See `DIRECTION.md` CURRENT DIRECTIVE,
> `PENDING_WORK.md` lap-146, `HANDOFF-2026-06-26-lap146.md`.

> **⭐⭐⭐ Lap-145 — `descent_step_Ind` CRACKED OPEN: `k=⟦t⟧` blocker DISSOLVED + descent PROVEN; real blocker = `zIndWff` antecedent gap (read FIRST — current).**
> Build re-verified 🟢 green (1326); headline `[propext, sorryAx, Classical.choice, Quot.sound]` (0 math
> axioms) — no drift. Attacked the lap-144 #1 hardest-first leaf `descent_step_Ind` (Ind-root soundness/descent)
> and took it apart. **THREE advances, two banked axiom-clean lemmas:** (1) the lap-144 "lone genuine
> prerequisite" — internal term-eval `k = ⟦t⟧` — is a **PHANTOM**: on the `∅→⊥` orbit `substs1 t p = ⊥` forces
> **`p = ⊥`** (`eq_falsum_of_substs1_falsum`: subst preserves the top connective, `^⊥` is its own only
> preimage), so every reduct premise exits at `⊥` for ANY `k`. (2) **DESCENT half DONE**
> (`iord_descent_iIndReductSeqG_one`): pinning the witness to `k = 1`, the genuine reduct `⟨d0,d1[a:=0]⟩`'s
> `iord` = the ordinal shadow `⟨d1,d0⟩`'s via a SINGLE `inadd`/`max` commute (both 2-element, `idg/iotil`
> substitution-invariant) → banked `iord_descent_iIndReduct` transfers; **`k=1` chosen to dodge `inadd_assoc`**
> (repo lacks it). (3) **THE finding — soundness blocked by a `zIndWff` GAP**: the reduct chain needs
> `seqAnt(fstIdx d1) ⊆ {⊥}`, but `zIndWff` gives only `inAnt (F(a)) (seqAnt(fstIdx d1))` (MEMBERSHIP, not shape)
> — a lax node (`d1` = `zAtom` of `{⊥,X}→⊥`) makes the goal genuinely FALSE, not just unprovable. **FIX (next,
> hardest-first):** strengthen `zIndWff` step clause to `seqAnt(fstIdx d1) = seqAddAnt (F(a)) Γ` (faithful Ind
> rule; lap-115/118-style ripple) → soundness closes, descent already done ⟹ DROPS `descent_step_Ind`.
> See `HANDOFF-2026-06-26-lap145.md`, `PENDING_WORK.md` lap-145.

> **🎉⭐⭐⭐ Lap-144 — LIVE PATH FULLY OFF `red` (executes DIRECTION lap-143 steps 2+3; a src sorry DROPS — read FIRST).**
> TWO advances: **(1) ¬-case CLOSED** — `descent_step_K_critical_neg` sorry-FREE + axiom-clean `[propext,
> Classical.choice, Quot.sound]`; the dispatcher `descent_step_K_critical` axiom-clean for BOTH polarities. The
> lap-142 `redexJ ≤ j0` obstruction dissolved via route (b): new `isChainInf_reduceR_keepTip` rebuilds chain-validity
> at the UNCHANGED ⊥-orbit tip `j0` when the §5 axNeg reduct lands above it (`⊥`-exit disjunct) — `haux0` needs
> threading only up to `j0`. **(2) Ind branch WIRED off `red`** — `ZDerivesEmptyR_descent_step`'s Ind root now calls
> the named `descent_step_Ind` (witness = genuine `iIndReductSeqG`), not `⟨red d, ZDerivesEmptyR_red, …⟩`. **Result:
> the ENTIRE live `false_of_ZDerivesEmpty` path is now off `red` — the headline's open `sorryAx` traces ONLY to
> honest TRUE-but-unproven lemmas (`descent_step_Ind`, `descent_step_K_noncritical`, (A)), NO kernel-FALSE statement.**
> **NEXT:** prove `descent_step_Ind` (Ind soundness via telescope `zKValidF` + term-value `k = ⟦t⟧`).
> See `HANDOFF-2026-06-26-lap144.md`, `PENDING_WORK.md` lap-144.

> **🧘 Lap-143 DEEP REFLECTION — direction KEPT; the existence-form pivot was half-ABANDONED, FINISH THE WIRING.**
> Re-verified in-kernel (green 1326): headline `[propext, sorryAx, Classical.choice, Quot.sound]` (0 math axioms),
> `goodsteinSentence_faithful`/`peano_not_proves_consistency` clean, statement re-audited — no drift. **The finding:**
> the lap-132 existence-form pivot (witness the bare-`∃` step with GENUINE reducts, NEVER `red`) was the right call —
> but laps 141-142 regressed it. `descent_step_K_critical` (`Crux2Blueprint:1891`) re-witnesses with
> `⟨red (zK …), ZDerivesEmptyR_red …⟩`, and `ZDerivesEmptyR_red` routes soundness through `redSoundGen` (:1471) —
> which is FALSE/incomplete (zInd case invokes the kernel-FALSE `zKValidF_iIndReduct_of_zInd` :80; zK case open :1508;
> critical via the kernel-FALSE `ZDerivation_red_zK_crit` :1108). So the live `false_of_ZDerivesEmpty` path still
> depends on two kernel-verified-FALSE sorries. The genuine red-free replacement `ZDerivation_iRKcCrit_critical_all`
> (:1847, lap-142, sorry-free) is BANKED BUT UNWIRED → zero false-dependence dropped (the "bank, don't wire"
> anti-pattern). **MANDATE (`DIRECTION.md` lap-143):** derive the ONE missing support lemma `ZSeqAnt_iRKcCrit`, split
> `descent_step_K_critical` into ∀ (wire `iRKcCrit`, dropping :80/:1108 for the dominant sub-case) + ¬ (named honest
> `redexJ≤j0` residual), then re-witness the Ind branch with `iIndReductSeqG`. FORBIDDEN = witnessing any descent
> branch with `red`. See `REFLECTION-2026-06-26-lap143.md`, `DIRECTION.md` CURRENT DIRECTIVE, `PENDING_WORK.md` lap-143.

> **⭐⭐⭐ Lap-142 — CRITICAL ∀-case soundness PROVEN via the genuine `iRKcCrit`, orbit-only [banked but UNWIRED — see lap-143].**
> `ZDerivation_iRKcCrit_critical_all` (sorry-FREE, `#print axioms`-clean) proves the critical ∀-case reduct
> `iRKcCrit` is a `ZDerivation` derived PURELY from `ZDerivesEmptyR + criticality` — reusing the banked per-reduct
> soundness `ZDerivation_iRKcCrit_all` (laps 112-119) with **NO `red`/`redSound` dependence** (so no false `:1108`
> instance-0 shadow) and **NO selection campaign**. This realizes the operator's existence-form spike end-to-end
> in kernel for the dominant critical sub-case. Unblocked by: the `zAxAll` ZPhi disjunct already carries
> `zAxAllSuccWff` (lap-130 "exact-shape obstruction" was STALE) → `redZKReady_of_zKValid` extended to yield
> `seqSucc sⱼ = cutFormula`; new `chainInf_redexI_data` gives `redexI < j0` + threading. **Remaining critical
> residual = the ¬-case's `redexJ ≤ j0`** (NOT free from `zKValid`; fix = pin `j0 = lh ds−1` on ⊥-orbit chains, or
> weaken `haux0_neg` threading). See `PENDING_WORK.md` lap-142. ↓ lap-141 below is superseded for the critical case.

> **⭐⭐ Lap-141 — SPIKE DECIDED: existence/critical-pair reframe OBVIATES the tag-5/6 wall.**
> The operator-mandated existence-form reframe spike was RUN and DECIDED in-kernel: `descent_step_K_critical`
> (sorry-FREE, compiles green) proves the reframe **does** obviate the tag-5/6 "cutPartner-is-principal-R-intro"
> residual — overturning lap-139 for that sub-case. Buchholz §3.2 splits the K-reduction CRITICAL/NON-CRITICAL
> (Def 3.2 5.1/5.2), NOT by major-premise tag; in the critical case **Lemma 3.1 hands back a PRINCIPAL pair for
> free** (no producer-principal proof), and the critical DESCENT is already banked
> (`iord_descent_red_zK_crit`). Restructured `descent_step_K_majorIdx` onto the split (case-split on the `permIdx`
> sentinel): the four `descent_step_K_tag{3,4,5,6}` sorries → ONE (`descent_step_K_noncritical`, Buchholz 5.2),
> producer-principal wall GONE. ⚠️ In-kernel CORRECTION (`#print axioms`, commit `0ee70e4`): the critical reduct
> is the SOUND `red` (= `iRcritG`), NOT the ordinal-shadow `iR2` — `descent_step_K_critical` routes soundness
> through the pre-existing red-R2 `ZDerivation_red_zK_crit` (1108), and the false-risk `iR2` sorry was DELETED.
> **Remaining wall: red-R2 (1108) + non-critical 5.2 (1865), both = Buchholz Thm 3.4.** See
> `HANDOFF-2026-06-26-lap141.md`, `PENDING_WORK.md` lap-141.

> **⭐⭐⭐ Lap-140 ALTITUDE REVIEW — crux-2 termination collapses to ONE lemma; lap-137 directive RETIRED [SUPERSEDED by lap-141].**
> Build re-verified 🟢 green (1326); headline re-verified `[propext, sorryAx, Classical.choice, Quot.sound]` (0
> math axioms), `goodsteinSentence_faithful` clean — no drift. **The altitude call:** laps 138-139 made the
> lap-137 CURRENT DIRECTIVE materially stale and it has been corrected in `DIRECTION.md`. Two stale mandates
> RETIRED: (1) the orbit (B)/(B0) it called "the load-bearing neglected piece" is **DONE** (lap 138,
> `exists_sigma1_iterate` via the repo's own `IIter.iIter`); (2) the `redLeast` μ-min route it mandated for (A)
> is **REFUTED** (lap 139 — a TOTAL `g:V→V` needs off-orbit completion whose graph has a Π₁ disjunct ⟹ `Σ₁∨Π₁`,
> wrong polarity; needs an unbuilt primrec witness bound). **The whole crux-2 termination now concentrates in
> ONE lemma `descent_step_K_majorIdx`** (`Crux2Blueprint:1764`): the M3 contradiction `false_of_ZDerivesEmpty`
> is sorry-free given `InternalPRWO V` (crux-1's deliverable, a hypothesis) + the bare-∃ per-step descent; the
> orbit (B) is proven; and (A) `exists_sigma1_descending_step` COLLAPSES into it via the *concrete* `redStep`
> route (lap-139 reconciliation: a concrete `𝚺₁` `redStep` gives `gDef` free, its descent clause IS
> `descent_step_K_majorIdx`). **MANDATE (DIRECTION.md):** decompose `descent_step_K_majorIdx` into its three
> per-tag {3 Ind, 4 chain, 5/6 ∀/¬-axiom} named src sub-`sorry`s (RAISES src count = progress), then ASSEMBLE a
> banked sub-piece to a DROPPED src sorry — the infra has been banked two laps; assemble, don't bank more.
> Hardest-first: tag-5/6 explicit-pair `iCritReductG` soundness (residual = cutPartner-is-principal-R-intro), or
> tag-3 `isChainInf_iIndReductSeqG` (readouts banked; pin the `t=t'+1`-vs-`numeral k` exit subtlety first).
> See `HANDOFF-2026-06-26-lap139.md`, `DIRECTION.md` CURRENT DIRECTIVE (lap-140), `PENDING_WORK.md`.

> **⭐⭐⭐ Lap-137 ALTITUDE REVIEW — the existence-form pivot's termination half was MIS-TYPED; FIXED (read FIRST — current).**
> Build re-verified 🟢 green (1326); headline re-verified in-kernel (`[propext, sorryAx, Classical.choice, Quot.sound]`,
> **0 math axioms**), no drift. **Where laps 135-136 left it:** the lap-132 existence-form reframe was run (lap 135)
> and PORTED to src — `false_of_ZDerivesEmpty` is a sorry-free composition of `descent_step_K_majorIdx` (per-step
> descent) + `prwo_forbids_existence_descent` (termination); lap 136 found the stated Ind reduct FALSE and built the
> corrected `iIndReductSeqG`. **THE altitude finding (decisive):** `prwo_forbids_existence_descent` concluded `False`
> in bare `[V ⊧ₘ* 𝗜𝚺₁]` with **NO PRWO/γ hypothesis** — **UNPROVABLE**: with the per-step descent `hstep`
> (= `ZDerivesEmptyR_descent_step`, a genuine `𝗜𝚺₁` cut-reduction fact) it would give `𝗜𝚺₁ ⊢ ¬∃z, ZDerivesEmptyR z`
> ≈ `Con(𝗣𝗔)`, Gödel-barred. PRWO(ε₀) is exactly the PA-unprovable principle and MUST be a hypothesis. The lap-136
> grind sank into the *other* (legitimately-`𝗜𝚺₁`) sub-sorry's Ind-reduct redesign while this structural hole sat
> undiagnosed. **FIXED this lap (green, banked):** new `InternalPRWO V` (no `𝚺₁` NF `ε₀`-descent — crux-1's
> deliverable, from `V ⊧ γ`); `prwo_forbids_existence_descent`/`false_of_ZDerivesEmpty` now sorry-FREE compositions
> taking `hprwo`; the genuine remaining termination content isolated as the NEW named sub-sorry
> `exists_sigma1_descent_of_step` (build the `𝚺₁` `ε₀`-descent: `redLeast` `μ`-witness over the `𝚫₁` matrix →
> internal `𝚺₁` orbit → `iord∘orbit`). Feasibility verified: `ZDerivesEmptyR` is `𝚫₁` (`zReg`/`zFresh`/`zSeqAnt`
> are `𝚺₁`-fns `= 0`), `iord` is `𝚺₁`. **NEXT (PRIMARY, hardest-first):** discharge `exists_sigma1_descent_of_step`
> — the never-built M3 internalization of the EXTERNAL-ℕ orbit (`iord_iR2_iterate_descends`, `InternalZ:9816`);
> it VALIDATES the whole existence-form pivot end-to-end. Secondary = `descent_step_K_majorIdx` (Ind-reduct +
> tag-4 chain). See `HANDOFF-2026-06-26-lap137.md`, `DIRECTION.md`, `PENDING_WORK.md` lap-137.

> **⭐⭐⭐ Lap-132 DEEP REFLECTION — direction KEPT, a structural course-TEST recommended (read FIRST — current).**
> Primary deliverable `REFLECTION-2026-06-26-lap132.md`. Build re-verified 🟢 green (1326); headline footprint
> re-verified in-kernel (`[propext, sorryAx, choice, Quot.sound]`, **0 math axioms**); statement re-audited vs
> source (`bump`/`goodsteinSeq` = genuine hereditary base bump; `goodsteinSentence_faithful` axiom-clean) — **no
> drift**. **The altitude finding:** the `red`-STALL that has driven the SELECTION campaign for ~12 laps (120→131
> — `firstBotPrem_reducible`, the `majorIdx` re-key, the tag-5/6 dispatch, the `zReg`/`zFresh`/`seqAntSeq` folds +
> ZPhi exact-shape strengthenings) exists ONLY because the endgame demands `red` be a *total deterministic Σ₁
> function* that descends on every orbit step; the fixpoint branch of `false_of_ZDerivesEmpty` then needs
> "`red`-fixpoint ⟹ cut-free", refuted for the permIdx engine (lap 129), forcing the whole no-stall campaign.
> **Reframe the iteration as `redLeast(d)` = the Σ₁ least *descending* reduct** (least `d'` with `ZDerivesEmptyR d'
> ∧ iord d' ≺ iord d ∧ d' a cut-reduct of d), and "`redLeast d = d`" ⟺ "no descending reduct" ⟹ "`d` cut-free" by
> the *contrapositive of a single existence lemma* (E), NOT by proving any selector faithful. (E) is discharged at
> the ⊥-root from already-banked facts: every ⊥-derivation's root is Ind/K (`zTag_Ind_or_K_of_ZDerivesEmpty`), the
> K-critical + Ind reducts are SOUND (laps 112-119) and DESCEND (`iord_descent_iRKcCrit_corr`/`_zInd`), cut-free
> ∅→⊥ is absurd (Cor 2.1, `tp_selected_isymRep_of_emptyAnt_botSucc`). **This obviates the permIdx-selection
> campaign** (the fixpoint→cut-free implication becomes definitional) **while REUSING the soundness, the invariant
> folds (`ZRegular_red`/`ZFresh_red` — needed in both forms), and the per-reduct descent lemmas.** Honest caveat:
> the redex-pair combinatorics survive (as a one-shot `∃`, not a total function); the spike must confirm (E) is
> clean at the root without re-importing the stall. **HIGHEST-VALUE NEXT TARGET:** a self-contained `wip/`
> spike (`ExistenceEndgame.lean`) — `redLeast` + (E) + the existence-form `false_of_ZDerivesEmpty` assembly,
> signatures pinned, bodies sorried where banked lemmas plug in. Decisive either way (mirror lap-101's fork spike).
> See `REFLECTION-2026-06-26-lap132.md`, `NEXT_STEPS.md`, `PENDING_WORK.md` lap-132.

> **⭐⭐⭐ Lap-129 FRESH-MIND REVIEW — DIRECTION CORRECTED: the genuine open crux is the `red`-STALL
> (termination), not reduct soundness; the lap-121/122 "no engine surgery" line is a DEAD END on the
> ⊥-orbit (read FIRST — current).** Build re-verified 🟢 green (1326); headline footprint re-verified
> in-kernel (`[propext, sorryAx, choice, Quot.sound]`, 0 math axioms). **THE finding (resolves lap-120's
> open question with a definitive NO):** the laps 104/107/120 `red`-STALL — `permIdx` selecting an
> atom/`Ax¹` leaf on a `∅→⊥` K-node, making it a `red`-FIXPOINT (`red_zK_fixpoint_of_atom_selected`) — is
> NOT vacuous and is NOT killed by `ZRegular`/`ZFresh`. Refuted in-kernel: `zReg (zAtom s) = 0` /
> `zReg (zAx1 s C) = 0` (atoms/`Ax¹` always regular; regularity only tracks eigenvariable freshness), and the
> `zAtom`/`zAx1` `ZPhi` disjuncts carry only `inAnt (seqSucc s) (seqAnt s)` — NO atomicity restriction — so a
> chain with an all-R-intro (`zIall`/`zIneg`) prefix + an atom whose succedent is a prior succedent satisfies
> `isChainInf` and is a valid ⊥-orbit `ZDerivation`. So `false_of_ZDerivesEmpty`'s "fixpoint ⟹ cut-free ⟹
> absurd" route FAILS (the fixpoint is NOT cut-free). **THE fix (Buchholz §14.25, source-read this lap):** the
> major premise of a `Θ→D` chain is *the first premise whose succedent IS `D`* (here `⊥`) — NOT the first
> `iperm`-permissible (`isymRep`) premise. `permIdx`/`iperm` is mis-designed (`iperm_isymRep` unconditional).
> **LANDED (axiom-clean, additive, green):** `firstBotPrem_reducible` (`InternalZ.lean`) — the faithful major
> premise (first `⊥`-exit) has `zTag ∉ {0,7}`, i.e. is `red`-reducible (NEVER a leaf-stall). Proof: the LEAST
> `⊥`-exit can't be a leaf (`chainAsucc_threaded_of_leaf` re-routes a leaf's `⊥` to a strictly earlier exit,
> contradicting leastness). **COURSE-CORRECTION:** the lap-121/122 redex-finder line
> (`inference_critical_pair_of_chain_reroute`, "dissolve the stall with no engine surgery") is mis-aimed for
> the ⊥-orbit — it needs a non-`isymRep` (L-symbol) exit, but ⊥-exits are `zK`/`zInd` (`isymRep`), so its
> residual `hreroute` for non-leaf `isymRep` is genuinely FALSE. Engine surgery (re-key `permIdx` to the
> faithful first-`⊥`-exit selection + recurse into the reducible major premise) IS required. **NEXT:** the
> faithful-selection engine re-key, with `firstBotPrem_reducible` guaranteeing no-stall. See
> `HANDOFF-2026-06-26-lap129.md`, `PENDING_WORK.md` lap-129, `NEXT_STEPS.md`.

> **⭐⭐⭐ Lap-128 — FRESHNESS CAMPAIGN completed; ∀-case SOUNDNESS of the engine-swap reduct LANDED (read
> FIRST — current).** A seven-commit arc: `ZFresh_red` (full `zK` dispatch) → `ZFresh` threaded into
> `ZDerivesEmptyR` (now a `red`-orbit invariant) → target-3 instance-`k` suppliers → `ZFresh_iRKcCrit` (O3
> front) → `zfresh_critReductCorr_freshness` (packages `⟨hpfresh,hΓfresh⟩` from the orbit) → **`ZDerivation_
> iRKcCrit_all`** (⭐ ∀-case soundness: `iRKcCrit (zK s r ds)` is a genuine `ZDerivation` with freshness
> discharged INTERNALLY from `ZFresh`, via the PROVEN `ZDerivation_iRcritG_critReductCorr`). The lap-114
> instance-`0`-vs-`k` obstruction is CLOSED on the supply side. **All three `iRKcCrit` invariants now
> landed:** O1 `ZRegular_iRKcCrit` (lap 119) + O3 `ZFresh_iRKcCrit` + ∀-soundness `ZDerivation_iRKcCrit_all`.
> **NEXT:** ¬-case soundness twin → discharge non-freshness plumbing (threading/rank from `isChainInf`) →
> assemble `ZDerivation_red_zK_crit` → the atomic engine swap (`iRKc ↦ iRKcCrit`). See
> `HANDOFF-2026-06-26-lap128.md`, `PENDING_WORK.md` lap-128.

> **⭐⭐⭐ Lap-127 — `zFresh_zsubst` PROVEN; `ZFresh_red` half-done (read FIRST — current).** The freshness
> invariant `zFresh` (lap 126) is now shown preserved by closed substitution: `ZFresh d → ZFresh (zsubst d a
> (numeral n))` — a **directional** law (NOT the equality lap-126 expected: substituting away an eigenvariable
> only LOWERS the violation count). The antecedent-wff gap (`ZDerivation` gives no entrywise `IsUFormula` at
> atom/`zAx1` leaves) was closed by **folding `seqWffFlag` into `freshFlag`**, so `zFresh` self-carries the
> well-formedness. `ZFresh_red_of_not_zK` (structural+Ind cases of red-stability) also landed. **NEXT:**
> `ZFresh_red_zK` (chain dispatch, mirror `ZRegular_red_zK` — should be EASIER, `zFresh(zK)` is pure
> premise-max-fold) → thread `∧ ZFresh` into `ZDerivesEmptyR` → close LEFT-branch ∀-soundness via
> `ZDerivation_iRcritG_critReductCorr`. See `HANDOFF-2026-06-26-lap127.md`, `PENDING_WORK.md` lap-127.

> **⭐⭐⭐ Lap-126 FRESH-MIND REVIEW — direction KEPT, MECHANISM corrected; the eigenvariable-freshness transfer substrate is LANDED (read FIRST — current).**
> Re-verified in-kernel (real `#print axioms`, green 1326): headline `peano_not_proves_goodstein =
> [propext, sorryAx, Classical.choice, Quot.sound]` (**0 math axioms**); the 4 new transfer lemmas
> axiom-clean `[propext, choice, Quot.sound]`. **Direction KEPT** (close the LEFT-branch ∀-soundness gap =
> the I∀ eigenvariable condition `hpfresh`/`hΓfresh`, lap-125's pin). **MECHANISM course-corrected:** the
> lap-125 baton proposed strengthening the `ZPhi` I∀ disjunct (64-site ripple) — but that **contradicts the
> repo's own lap-93 additive-O1 architecture** (`Zsubst.lean:947`: do NOT bake freshness into `zIallWff` —
> it shrinks the `ZDerivation` fixpoint + forces the embedding to re-prove it) and would break the proven
> `ZDerivation_zsubst` (a code bound is not `zsubst`-stable, lap-92). **The principled fix = a standalone
> `zFresh` invariant** (exact parallel of `zReg`), storing the `𝚫₁`, `zsubst`-stable *semantic*
> non-occurrence `fvSubst a (numeral 0) p = p`. **LANDED this lap (`Zsubst.lean`):** the
> double-substitution-collapses substrate `termFvSubst_numeral_idem` / `termFvSubstVec_numeral_idem` /
> `fvSubst_numeral_idem` + the transfers `fvSubst_numeral_transfer` (`fvSubst a (numeral m) p = p → fvSubst
> a (numeral k) p = p`) and `fvSubstSeq_numeral_idem`/`fvSubstSeq_numeral_transfer` — which plug DIRECTLY
> into `ZDerivation_iRcritG_critReductCorr`'s `hpfresh`/`hΓfresh` at the cut instance `k`. **NEXT:** define
> the standalone `zFresh` (mirror `zReg`) + per-node extraction + `zFresh_zsubst` stability + thread into
> `ZDerivesEmptyR`. See `PENDING_WORK.md` lap-126, `HANDOFF-2026-06-26-lap126.md`.

> **⭐⭐⭐ Lap-120 DEEP REFLECTION — the genuine open crux is the SELECTION/STALL defect; the inversion is a solved side-problem (historical).**
> Primary deliverable `REFLECTION-2026-06-26-lap120.md`. Build re-verified green (1326); headline + girder
> re-verified in-kernel (`[propext, sorryAx, choice, Quot.sound]`, 0 math axioms); statement re-audited vs
> paper — no drift. **THE finding:** the endgame `false_of_ZDerivesEmpty` (`Crux2Blueprint:1144`, bare sorry)
> cannot close because **`red` STALLS** — `permIdx` can select an atom/`zAx1` premise (`iperm isymRep` is
> unconditionally true), making a tag-4 K-node a `red`-FIXPOINT that is NOT cut-free. The repo flags this in
> `RedZKDescent.lean`'s own words; lap-111's disjunctive `iord_descent_red` did NOT fix it, it RELOCATED it
> into the `false_of_ZDerivesEmpty` sorry (the stall branches close on `Or.inl`). This is the SAME defect
> diagnosed at laps 104/107 ("`red` stalls after one K-reduction"), still open 13 laps later. The inversion
> work (112–119) is real progress on a DIFFERENT sub-problem (reduct SOUNDNESS); soundness ≠ termination.
> **HIGHEST-VALUE NEXT TARGET (course correction):** confront **(A)** `red w = w ∧ ZDerivesEmptyR w ⟹ False`
> (a `red`-fixpoint on the ⊥-orbit is absurd) — attempt the VACUITY resolution first (an atom-/`zAx1`-selected
> K-node concluding `∅→⊥` is impossible by sequent shape; probe whether `ZRegular` already kills it). It is
> contained, additive, on the M3 critical path, independent of the swap, and DECISIVE either way — it tests
> whether the internalized cut-elimination actually terminates to a contradiction. **STOP** treating the
> atomic engine swap as the sole next target before this is de-risked. See `REFLECTION-2026-06-26-lap120.md`,
> `NEXT_STEPS.md`, `PENDING_WORK.md` lap-120.

> **⭐⭐ Lap-119 — the engine swap is NOT "pure wiring"; its O1 (regularity) front LANDED (historical).**
> The lap-118 baton's "all-banked → pure wiring" engine-swap plan OMITTED the `ZRegular`/O1 front entirely.
> Swapping `red`'s critical value to `iRKcCrit` breaks `ZRegular_red_zK_crit` (premises become
> `zsubst`/`zInegPrem`/`zAx1`, not `zAxReduct∘red`), and `ZRegular_red` is load-bearing (→ `ZDerivesEmptyR`).
> Reverted the swap (kept `src/` green), landed the missing front additively: **`ZRegular_zsubst_zIallPrem`**,
> **`ZRegular_zInegPrem`**, **`ZRegular_iRKcCrit`** (whole corrected reduct regular; `zReg_zsubst` already
> existed). All axiom-clean. Swap now correctly scoped into 3 fronts (O1 de-risked / descent re-key /
> soundness+orbit). InternalZ swap half saved as `scratchpad/lap119-engine-swap.diff`. See
> `HANDOFF-2026-06-26-lap119.md`.

> **⭐⭐⭐ Lap-118 — the ¬-case inversion's last residual DISCHARGED; capstone now UNCONDITIONAL (read FIRST — current).**
> Lap 117 proved the ¬-case critical-cut inversion SOUND but carried one orbit hypothesis `hpmem : inAnt A
> (seqAnt sⱼ)` (Buchholz 2.2's `A,¬A∈Γ`). This lap discharges it by **strengthening the `zAxNeg` (tag-6) ZPhi
> disjunct** with a 4th conjunct `inAnt p (seqAnt s)` — making the repo's ¬-axiom faithful to Buchholz §5 case
> 2.2, where `Ax^{¬A,0}` genuinely carries BOTH `A,¬A∈Γ` (scratchpad `buchholz-gentzen.txt:903`). Ripple done
> (ZPhi/`zphi_monotone`/`_strong_finite`/`zphi_iff`/`zblueprint` σ+π/`zPhi_definable` + the rcases sites);
> `zDerivation_zAxNeg_inv` now returns both memberships. `ZDerivation_corrected_haux0_neg` recovers `hpmem`
> in-proof (`zDerivation_zK_inv` + `zDerivation_zAxNeg_inv`), so **`ZDerivation_iRcritGNeg_corrected_neg` drops
> the `hpmem` hypothesis** — all axiom-clean `[propext, Classical.choice, Quot.sound]`, build 1326. This is the
> ¬-side twin of lap-115's `zAx1` 8th-disjunct discharge (which closed the ∀ L-half's `hZredL`). **NEXT (the
> engine re-key, now fully de-risked on BOTH polarities):** re-key `red`'s tag-4 critical branch (`iRKc`,
> `InternalZ:6656`) to DISPATCH on redex polarity and emit `iRcritG`+`critReductCorr` (∀) / `iRcritGNeg`+ρ_neg
> (¬). Both soundness capstones are now hypothesis-light. See `HANDOFF-2026-06-26-lap118.md`.

> **⭐⭐⭐ Lap-117 — the ¬-case critical-cut inversion SOUNDNESS PROVEN; BOTH critical sub-cases now complete (read FIRST — current).**
> The lap-116 ∀-case (`iRcritG`/`critReductCorr`) had a documented CAVEAT: it handled only the I∀ R-redex; the
> I¬ R-redex was open. This lap closes it — and surfaces the genuine reason it is NOT a mechanical mirror.
> **THE structural finding (Buchholz Def 3.2 case 5.1, ¬-subcase):** for a cut on `¬A` the two half-derivations
> SWAP polarity — `d{0}` (succedent `Π.A`) replaces the **L**-redex `j` (axNeg), `d{1}` (antecedent `A,Π`) the
> **R**-redex `i` (I¬) — the OPPOSITE of the ∀-case. The repo's `iRcritG` (∀-convention `seqUpdate` slots) cannot
> express this, so a new **swapped-half constructor `iRcritGNeg`** (InternalZ) is required. Built + proven sound,
> all axiom-clean `[propext, Classical.choice, Quot.sound]`:
> - `iRcritGNeg` + `ZDerivation_iRcritGNeg_of` (InternalZ): swapped-half reduct + assembly.
> - `ZDerivation_corrected_haux0_neg` (succedent half): redexJ=axNeg ↦ §5 reduct `Ax^1_{Γⱼ→A}` (Buchholz Lemma
>   5.1 case 2.2), via `iCritReplaceReduce_of`.
> - `ZDerivation_corrected_haux1_neg` (antecedent half): redexI=I¬ ↦ child `d0` (`A,Γᵢ→⊥`), via
>   `iCritReplaceReduce_general` + `isChainInf_reduceR_membership` (the `⊥`-tip re-point makes arbitrary
>   conclusion succedent OK — why the I¬ child fits a non-`⊥` endform chain).
> - `ZDerivation_iRcritGNeg_corrected_neg`: the ¬-case soundness capstone.
> **ONE documented §5 residual:** `hpmem : inAnt A (seqAnt sⱼ)` — Buchholz 2.2's side condition `A,¬A∈Γ`, of
> which the repo's `zAxNeg` ZPhi disjunct supplies only `¬A∈Γ` (`zDerivation_zAxNeg_inv`). Discharge = strengthen
> the `zAxNeg` disjunct to carry both `A,¬A` (the L-side analogue of lap-116's `zAx1` 8th-disjunct), OR derive
> `A∈Γⱼ` from the redex-pair chain context.
> **NEXT (the engine re-key, now de-risked):** with BOTH ∀ (`iRcritG`/`critReductCorr`) and ¬ (`iRcritGNeg`)
> soundness proven, re-key `red`'s tag-4 critical branch to DISPATCH on the redex polarity (`zIall` redexI →
> `iRcritG`+`critReductCorr`; `zIneg` redexI → `iRcritGNeg`+the ¬-reducts) and emit the correct constructor.
> Then `ZDerivation_red_zK_crit` closes via `red_zK_crit` + the two soundness capstones, and the descent
> re-points (ρ-invariant via `iord_iRcritG_eq_iRcrit`; needs an `iRcritGNeg` iord-invariance twin). See
> `HANDOFF-2026-06-26-lap117.md`, `PENDING_WORK.md` lap-117.

> **⭐⭐⭐ Lap-115 — the inversion's L-half PROVEN; remaining gate = make `zAx1` a sound ZDerivation (historical).**
> Both halves of the corrected critical-cut inversion are now axiom-clean: R-half `ZDerivation_corrected_haux0`
> (lap 114) + **L-half `ZDerivation_corrected_haux1`** (`Crux2Blueprint`, this lap). Grounded the L-side in
> **Buchholz §5 case 2.1** (scratchpad `buchholz-gentzen.txt:903`): the L-redex `axAll` axiom `Ax^{∀p,k}` (which
> has succedent `F(k)`) reduces to the §5 **logical axiom** `dⱼ[0] = Ax^1_{F(k),Γⱼ→F(k)}` — antecedent GAINS
> `F(k)=cutFormula d`, succedent `F(k)` (so it IS a genuine logical axiom, succedent ∈ antecedent). Engine
> `v = zAx1 (seqAddAnt (cutFormula d) sⱼ) C`. `haux1` is discharged via `ZDerivation_iCritReplaceReduce_general`
> (antecedent-growth replace; `tp v=isymRep`, `zTag v=7` ⟹ all tag conjuncts vacuous) modulo **two named §5
> residuals**: (O-L1) `hZredL` — that `zAx1 …` is itself a `ZDerivation`; (O-L2) `hci` — the threading
> reconstruction `isChainInf`. **THE crux finding (extends lap-114 to the L-side):** the engine's L-redex reduct
> `zAxReduct (zAxAll sⱼ p k') = zAx1 sⱼ p` is unfaithful in THREE ways — payload `p` vs `F(k)`, sequent `sⱼ` vs
> `seqAddAnt F(k) sⱼ`, AND **`zAx1` (tag 7) is NOT a `ZPhi` disjunct, so it is not a `ZDerivation` at all**.
> **NEXT (the gate for BOTH halves → the inversion):** make `zAx1 s C` a sound ZDerivation leaf — the §5 `Ax^1`
> logical axiom, validity `inAnt (seqSucc s) (seqAnt s)` (succedent ∈ antecedent, mirroring `zAtom`). This is an
> 8th `ZPhi` disjunct (ripples: `zphi_monotone`/`_strong_finite`/`zphi_iff`/`zblueprint` σ+π/`zPhi_definable`
> + ~64 `rcases zDerivation_iff.mp` sites, each +1 trailing tag-7 arm). Then `hZredL`/(O-L1) discharges; `hci`/
> (O-L2) is the lap-113 `irk_chainAsucc` threading at `redexJ`. See `HANDOFF-2026-06-25-lap115.md`.

> **⭐⭐⭐ Lap-114 FRESH-MIND REVIEW — the cut-elimination PRIZE is FEASIBLE (re-principalization), not a multi-year wall (read FIRST — current).**
> Baton `ANALYSIS-2026-06-25-lap114-inversion-instance-mismatch.md`. Build 🟢 green (1326); headline footprint
> re-verified in-kernel (`[propext, sorryAx, choice, Quot.sound]`, 0 math axioms). **The crux-2 prize**
> `ZDerivation_red_zK_crit` (`Crux2Blueprint:100`) — the critical-cut SOUNDNESS inversion, framed since lap
> 110 as "the multi-year cut-elim core (`Zinfty.allInv`)" and the avoided piece (lap-111) — is **FALSE as
> stated, for a precise FIXABLE reason.** It reduces (via `ZDerivation_iRcritG_of`; outer chain validity is
> automatic) to two stripped halves `haux0`/`haux1`. `haux0` concludes `Γ → cutFormula d = Γ → F(k)` (k = the
> L-redex axAll instance); its `isChainInf` threading forces the redexI premise to derive `F(k)`. But `red`'s
> reduct there is `zsubst d0 a (numeral 0)` (instance **0**, `red_zIall`), deriving `F(0) ≠ F(k)`. **`red`'s
> critical reduct is unsound — it loses the cut instance.** (Instance-0 is correct for the ordinal DESCENT —
> `iord` is instance-invariant, so `iord_descent_red` survives — which is exactly why this hid through laps
> 108–113.) This is lap-104's `red_redAllEx_eq` re-principalization finding, now pinned to the live engine.
> **FIX (contained; building blocks BANKED):** the R-redex (I∀) premise must be `zsubst d0 a (numeral k)`;
> its succedent `= cutFormula d` by the new **`seqSucc_zsubst_zIall_premise`** (`Zsubst.lean`, axiom-clean —
> the linchpin landed this lap), it is a `ZDerivation` by `ZDerivation_zsubst_zIall_premise` (banked), and I¬
> needs no change. So the inversion is a `red`-redefinition (re-key `iRNextG` tag-4 to substitute the L-redex
> `k`), NOT new deep machinery; the descent transfers (instance-invariant). **NEXT:** implement the corrected
> reduct + prove `haux0`/`haux1` (threading) → real `ZDerivation_red_zK_crit` → `redSound`. See
> `PENDING_WORK.md` lap-114.

> **⭐⭐⭐ Lap-113 — splice `hr'` degree-drop PROVEN; gap isolated to the chain-rank invariant (historical).**
> Baton `HANDOFF-2026-06-25-lap113.md`. Build 🟢 green (1326). The lap-112 cut-formula strip now drives the
> splice descent **end-to-end in-kernel**: `iCrit_halves_descend` gained a 7th conjunct
> `irk (seqSucc (fstIdx (znth (zKseq (red (zK s r ds))) 0))) < r` (via the e0 succedent = `cutFormula`
> readout + `irk_cutFormula_lt`, T3.4(a) strict drop; redex R-principal put in `chainAsucc` form by global
> R-permissibility). `iord_descent_red`'s splice branch now **closes `hr'` fully** — all `idg`/`iseqMaxIdg`
> arithmetic PROVEN — so it drops from 2 internal sorries to **1** (only the chain-REPLACE IH remains).
> The lone splice residual is now a single clean Buchholz-standard statement **`irk_chainAsucc_redexI_le`**
> (`Crux2Blueprint:549`): `zKValid ⟹ irk (chainAsucc ds redexI) ≤ r`. **THE next campaign:** it needs
> `redexI < j₀` (chain exit index), true once `j₀ = lh ds − 1` (every premise threaded, as
> `isChainInf_of_last` builds them) — but `isChainInf` only promises `∃ j₀ < lh ds`, so a redex could sit
> in the un-threaded tail `(j₀, lh ds)`. Faithful fix = strengthen `isChainInf`'s exit invariant to the
> last premise (ripples through its 𝚫₁-def + every reduct's chain-validity; 63 refs → its own campaign).

> **⭐⭐⭐ Lap-111 DEEP REFLECTION — direction KEPT, ONE structural lever identified (read FIRST — current).**
> Primary deliverable `REFLECTION-2026-06-25-lap111.md`. Build 🟢 green (1326); statement re-audited vs paper
> (no drift); headline + `goodstein_implies_consistency` + `peano_not_proves_consistency` + faithfulness anchor
> all re-verified in-kernel (`lake env lean`). **Findings:** (1) lap 110 was NOT circling — it produced a genuine
> kernel-grounded root cause (`iCritReductG` cuts the critical reduct on the PRINCIPAL `A_i`; Buchholz 3.4(a)
> cuts on the STRIPPED `A(d)`, strictly lower rank). (2) But the work is IMBALANCED: the ordinal-DESCENT
> bookkeeping (`iord_descent_red`, ~80% done) has soaked up the laps while the genuine cut-elimination
> CONTENT — the ∀/¬-INVERSION (`ZDerivation_red_zK_crit`, ≈0% on the engine; its only attempt `ZInf.allInv`
> was killed VACUOUS at lap 107) — sits untouched. The inversion is the prize and it is the avoided piece.
> (3) The `iord_descent_red` FIXPOINT branches (atom/axAll/axNeg-selected, `red d = d`; + the chain-REPLACE IH
> false-at-fixpoint) are a SELECTION bug masquerading as descent gaps — the same "engine stalls after one step"
> defect re-surfacing branch by branch (laps 104/107/109/110). **HIGHEST-VALUE STRUCTURAL MOVE (do first):**
> reformulate `iord_descent_red` to the disjunctive `red d = d ∨ iord ≺` and `false_of_ZDerivesEmpty` to
> "terminate-at-cut-free ⟹ absurd" — the fixpoint branches then close TRIVIALLY (left disjunct) and the whole
> remaining crux-2 obligation sharpens to `red d = d ⟹ cut-free` (selection correctness) + `no cut-free ∅→⊥` +
> the inversion. Contained: `iord_descent_red` is consumed only via `iord_red_iterate_descends →
> false_of_ZDerivesEmpty`. **Then** land lap-110's cut-formula strip (closes `hr'`), **then** the inversion
> (the prize). Doc-drift fixed: `Reduction.lean` no longer claims `peano_not_proves_consistency` carries
> `PA_delta1Definable` (kernel-clean since lap 89). See `REFLECTION-2026-06-25-lap111.md`, `NEXT_STEPS.md`,
> `HANDOFF-2026-06-25-lap111.md`, `PENDING_WORK.md` lap-110.

> **⭐⭐⭐ Lap-110 — splice branch 6/7 CLOSED (`iCrit_halves_descend`); `hr'` degree-drop crux isolated (historical).**
> Baton `HANDOFF-2026-06-25-lap110.md`. Build 🟢 green (`lake build GoodsteinPA`, **1326**); headline footprint
> intact (`peano_not_proves_goodstein = [propext, sorryAx, Classical.choice, Quot.sound]`, 0 math axioms;
> `iCrit_halves_descend` axiom-clean `[propext, choice, Quot.sound]`). Banked `iCrit_halves_descend`
> (`RedZKDescent.lean`): the two critical-reduct halves descend below `dᵢ` because each is a `K`-chain over
> `dᵢ`'s own premise seq with the redex R/L premise swapped for its descending reduct (the critical `õ`-jump is
> in the OUTER `K^{r-1}` rank-drop, NOT the halves). Wired into `iord_descent_red`'s splice branch
> (`Crux2Blueprint:595`), closing 6 of its 7 sub-`sorry`s. **The lone splice residual is the rank bound
> `hr' : max(irk C) r ≤ idg(parent)`** with `C` the redex principal formula — fails by ONE in the edge case
> `irk C = r'ᵢ = idg(dᵢ) = iseqMaxIdg ds`; needs a STRICT chain-rank-vs-degree invariant or a measure/rank
> refinement (PENDING_WORK lap-110, two paths). Other open K-case residuals: chain-REPLACE IH (atom-fixpoint
> wall, lap-109) + atom/axAll/axNeg fixpoints. See `HANDOFF-2026-06-25-lap110.md`, `PENDING_WORK.md` lap-110.

> **⭐⭐⭐ Lap-107 FRESH-MIND REVIEW — DIRECTION CHANGE: the external-inductive prototype track is a DEAD END (read FIRST — historical).**
> Baton `HANDOFF-2026-06-25-lap107.md`. Build 🟢 green (1325); `src/` UNTOUCHED (headline footprint intact,
> re-verified in-kernel: `peano_not_proves_goodstein = [propext, sorryAx, Classical.choice, Quot.sound]`,
> 0 math axioms; `peano_not_proves_consistency` / `not_proves_of_implies_consistency` axiom-clean
> `[propext, Classical.choice, Quot.sound]`). Two kernel-verified findings overturn the lap-102→106 plan:
> **(1) `ZInf.allInv` is VACUOUS** — provable by a SINGLE weakening (`ZInf.weaken_top d.seq d`), ignoring
> both `ht` and the `^∀φ` membership (confirmed by elaborating the one-liner in place of the lap-106
> `induction`; `wip/PathCInf.lean`, now `ZInf.allInv_vacuous`). Root cause: the META `Zinfty.allInvAux`'s
> content is **ordinal preservation** + **erasure** of `^∀φ`, and `ZInf : V → Prop` has neither — so the
> lap-106 work + the planned `permCongr` perf fix were content-free. **(2) External inductives are
> NON-LOAD-BEARING** — `ZInf`/`ZcOK`/`ZcDer` are all external Lean inductives (a deferred-arithmetization
> PROTOTYPE, PathCOmega.lean:701); the headline `IΣ₁ ⊢ Con(PA)` needs the descent in EVERY `V ⊧ IΣ₁`,
> including non-standard models whose coded ⊥-proof is non-standard (no external well-founded tree exists),
> so `foundation_bot_to_Z_empty` is unprovable on them. **The load-bearing carrier is the Σ₁ CODE engine
> `red`/`iord` (`InternalZ.lean`).** THE crux (re-confirmed lap-104): engine `red` steps via `iRNextG`,
> dispatching ONLY on the top `zTag`, so after one K/cut reduction it stalls ⟹ `iord_descent_red`
> (`Crux2Blueprint.lean:533`) is unprovable for the current `red`. **NEXT (hardest-first):** redesign
> `red`/`iRNextG` to find + key-reduce the lowest cut anywhere in the ∅→⊥ derivation code (the prototype
> inversion cases are the combinatorial GUIDE), prove `iord_descent_red`, then `false_of_ZDerivesEmpty` via
> the `iord`-descent + PRWO → headline. Prototypes (`PathCInf`/`ZcDer`/`ZcOK`) stay as a sketch — no further
> investment. See `HANDOFF-2026-06-25-lap107.md`, `NEXT_STEPS.md`, `PENDING_WORK.md` lap-107.

> **⭐⭐⭐ Lap-106 — conclusion-tracking `ZcDer` DONE + the ∀-inversion recursion STARTED on `ZInf` (historical — see lap-107 box above).**
> Baton `HANDOFF-2026-06-25-lap106.md`. Build 🟢 green (1325); `src/` UNTOUCHED (headline footprint intact:
> `peano_not_proves_goodstein = [propext, sorryAx, Classical.choice, Quot.sound]`, 0 math axioms). Closed
> lap-105's NEXT prerequisite (conclusion-tracking): `inductive ZcDer` (= `ZcOK` + ω-∀ conclusion data) +
> forgetful `ZcDer.toZcOK` + conclusion-faithful principal ∀-inversion (`zcDer_iord_descent_allOmega`) +
> embedding realization (`zIall_realizes_ZcDer`) + principal-cut orbit step + the full per-node
> inversion-step family (`wip/PathCOmega.lean`, bricks 5o–5q). Then STARTED the genuine deep core in NEW
> `wip/PathCInf.lean`: `inductive ZInf` — the arithmetized one-sided Tait Z∞ derivation (V-internal port of
> `Zinfty.Deriv`, 9 constructors, strictly-positive ω-rule ⟹ full structural recursor), and **`ZInf.allInv`,
> the ∀-inversion recursion (port of `Zinfty.allInvAux`) with its STRUCTURE + the PRINCIPAL `allω` case +
> atomic bases machine-checked** (bricks 5r–5s). The lone open obligation: `allInv`'s COMMUTING cases carry
> a disclosed `sorry` — a term-mode HFS-`whnf` perf blowup (NOT a math gap; the verbatim `allInvAux` port
> times out under `induction` from implicit-arg unification). NEXT (hardest-first): the `permCongr`/
> explicit-arg perf fix to discharge the six commuting `sorry`s, then `andInv`/`orInv`/`cutElim`, then bridge
> `ZInf`-height ↔ engine `iord` for the PRWO descent, then wire to `false_of_ZDerivesEmpty`
> (`Crux2Blueprint.lean:588`) → headline. See `HANDOFF-2026-06-25-lap106.md`, `NEXT_STEPS.md`, `PENDING_WORK.md`.

> **⭐⭐⭐ Lap-105 — the natural-sum `#` RESOLUTION of the lap-104 `imax` tension (historical — see lap-106 box above).**
> Baton `HANDOFF-2026-06-25-lap105.md`. Build 🟢 green (1325); `src/` UNTOUCHED (headline footprint intact:
> `peano_not_proves_goodstein = [propext, sorryAx, choice, Quot.sound]`, 0 math axioms). Lap-104's 2nd
> in-kernel finding (the `imax` stored ordinal can't satisfy the cut node's operator-control, since the
> max-ACHIEVING premise EQUALS `imax`) framed the fix as Gentzen's `ω`-tower, "multi-month". **This lap shows
> that deferral is unnecessary for the principal ∀/∃ step.** The natural (Hessenberg) sum `inadd` (`#`,
> already in `InternalNadd.lean`) supplies BOTH obligations at once (5 new axiom-clean lemmas in
> `wip/PathCOmega.lean`): operator-control from STRICT SELF-DOMINATION (`X ≺ X#g` for `g≻0`,
> `lt_inadd_self_right`/`_left`), and descent from STRICT MONOTONICITY (`a≺a' → b≺b' → a#b ≺ a'#b'`,
> `inadd_strict_mono`). `zcOK_redAllExN` closes the operator-control half of `hinv` for the principal ∀/∃ cut
> with NO assumed `hLctrl`/`hRctrl` (contrast lap-104's `zcOK_redAllEx_of_ctrl`); `sord_redAllExN_lt` gives
> the per-step descent **against a `#`-stored parent with NO additive-principality needed** — precisely the
> obstruction that drove lap 104 to `imax`. **The `ω`-tower is now isolated to its true locus: rank-mixing
> across COMPOUND cut formulas (∧/∨, where one cut spawns two lower-rank cuts), NOT the ∀/∃ principal step.**
> NEXT (hardest-first): general ∀-inversion `redInv∀` (re-principalize non-ω-∀ left premises), then the
> internal `iomegaTower` for the compound cases. See `HANDOFF-2026-06-25-lap105.md`, `NEXT_STEPS.md`.

> **⭐⭐⭐ Lap-104 FRESH-MIND REVIEW + IN-KERNEL ENDGAME CORRECTION (historical — see lap-105 box above).** Baton
> `HANDOFF-2026-06-25-lap104.md`. Build 🟢 green (`lake build GoodsteinPA`, 1325); `src/` UNTOUCHED (headline
> footprint intact — re-verified in-kernel `lake env lean`: `peano_not_proves_goodstein = [propext, sorryAx,
> choice, Quot.sound]`, **0** math axioms; `peano_not_proves_consistency` clean; `not_proves_of_implies_consistency`
> clean). **Direction KEPT** (headline = crux-1 DONE ∘ crux-2 = the Gentzen ordinal-analysis girder, via the
> Path-C single-step `red` descent + PRWO(ε₀)). **But the lap-103 endgame packaging is CORRECTED by an
> in-kernel certificate.** Lap 103 reduced crux-2 to `red_iterate_descends`'s three hypotheses (`hinv`/`hdrop`/`hz`)
> and framed `hinv` (orbit invariant `red`-closed) as "tractable via premise selection". **That framing is
> false, now PROVEN false in-kernel** (4 new axiom-clean lemmas in `wip/PathCOmega.lean`): the ∀/∃-cut reduct
> `redAllEx` selects the ω-∀-node's BASE premise `zsubst d0 a t` as its new left premise, whose tag is
> `= zTag d0 ∈ {0..6}` (`zTag_zsubst`), **never** the stored-ω-∀ tag `7` (`zTag_ne_seven_of_ZDerivation`). So
> `red` is the IDENTITY on the reduct (`red_redAllEx_eq`), the orbit STALLS after one step
> (`sord_red_iterate_stalls_AllEx`: `sord` constant from step 1 — no infinite descent), and ANY dispatch-shaped
> `P` is provably NOT `red`-closed (`naive_dispatch_P_not_red_closed`). **Consequence (the corrected next
> brick):** the reduct's premises (`zsubst d0 a t` / `zExPrem dR`) are not principal nodes for the smaller cut
> on `F(t)`; to keep the orbit reducible `red` must RE-PRINCIPALIZE them via Schütte/Tait **INVERSION**
> operators (`redInv∀`/`redInv∧`/…). `hinv` IS the Hauptsatz (inversion + reduction), not naive selection —
> and inversion is a recursion over the derivation, so it needs the genuine **Path-C derivation predicate
> (the datatype, NEXT_STEPS step 1)**. STOP adding `hdrop` cut-shape cases (easy leaves on an unsatisfiable
> `hinv`); START the datatype + inversion. See `HANDOFF-2026-06-25-lap104.md`, `PENDING_WORK.md` lap-104,
> `NEXT_STEPS.md`.

> **⭐⭐⭐ Lap-102 — Probe 2 EXECUTED, the fork is SETTLED (historical — see lap-104 box above).** Baton
> `HANDOFF-2026-06-25-lap102.md`; verdict + 3 new axiom-clean lemmas in `wip/InternalZomega.lean`. Build
> 🟢 green (1325). The lap-101 fork (finitary Path X vs ω-rule Path C) is resolved IN FAVOUR of **Path C**,
> with a refinement that overturns lap-101's cost estimate: (A) the chain/`redZKReady` motive is RETIRED —
> `Zinfty.lean` already proves full ω-rule cut-elimination with no chain; (B) **the ordinal layer must be
> REPLACED, not reused** — `iotil_zK_iIndReduct_strictMono` proves the induction ω-node's premise ordinals
> strictly increase in unfolding depth, so its ordinal is a genuine LIMIT the computed `iord` (finite
> `#`-fold, no sup) cannot assign. Path C = **Buchholz operator-controlled derivations with STORED
> ordinals** (`ZinftyF.Deriv`/`o` shape, arithmetized). Path X disfavoured AND likely broken (hereditary-Rep
> fails down a nested-chain spine; Cor 2.1 fires only at the ∅→⊥ top node). **NEXT = begin the Path-C
> arithmetized stored-ordinal datatype** (`NEXT_STEPS.md` PRIORITY 1). `src/` unchanged; headline footprint
> intact (`peano_not_proves_goodstein` = 0 math axioms, lone `sorryAx` = crux-2). Keep Path X green in
> `src/` as fallback.

> **⭐⭐⭐ Lap-101 DEEP REFLECTION (historical — see lap-102 box above).** Primary deliverable
> `REFLECTION-2026-06-25-lap101.md`. Re-verified kernel in-kernel (`lake env lean`, green 1325): headline
> `peano_not_proves_goodstein = [propext, sorryAx, Classical.choice, Quot.sound]` (**0 math axioms**),
> `peano_not_proves_consistency = [propext, choice, Quot.sound]` (clean), faithfulness anchor
> `goodsteinSentence_faithful` clean; statement re-audited vs the paper (`goodsteinSeq` = genuine hereditary
> base bump; `bump` recurses on exponents) — **no drift**. **Destination KEEP, crux-2 target KEEP — but the
> SUB-ROUTE fork is reopened.** The lap-92 reflection diagnosed the *finitary* presentation as the wall-source
> and recommended an ω-rule pivot (Path C) **after a de-risk spike**; lap-95 overruled to Path X (finitary)
> **without running that spike**, and laps 95–100 did not dissolve the wall — they *relocated* it from
> eigensubst (O2) to the `redZKReady` "hereditary all-Rep selected spine" motive, exactly the
> conclusion-tracking the ω-rule makes free. Worse, the motive's hard core looks shaky: a ∅→⊥ chain's premises
> have *growing* antecedents `{A₀..A_{i-1}}→Dᵢ`, so Cor 2.1 does NOT directly reapply to the selected premise
> ⟹ "hereditary all-Rep" is a repo artifact (keeping `Π` + `tpReduce`) that may not hold as stated. **CALL:
> run the skipped spike** `wip/InternalZomega.lean` — internal ω-rule ∀-node + substitution-free critical-cut
> reduct, confirm by elaboration. Elaborates clean → PIVOT to Path C (retires the whole finitary obligation
> list — motive/axNeg/Ind/5.1/5.2.1/ordinal-K — at once; math doubly-proven by Bryce–Goré + the repo's own
> axiom-clean meta `Zinfty.lean`). Walls on Σ₁-arithmetization → commit to Path X with evidence. **STOP**
> sinking laps into the `redZKReady` motive / axNeg until the spike's verdict. Keep Path X infra in `src/`
> (green, fallback). See `NEXT_STEPS.md`, `PENDING_WORK.md` lap-101.

> **⭐⭐⭐ Lap-98 FRESH-MIND REVIEW (historical — see lap-101 box above).** Re-verified kernel (real `#print axioms`,
> green 1325): headline `peano_not_proves_goodstein = [propext, sorryAx, Classical.choice, Quot.sound]`
> (bare `sorry`; the lone math residual `sorryAx` = crux-2), `peano_not_proves_consistency` clean.
> **Direction KEPT — and the obvious-looking alternative was actively REFUTED, not assumed.** This lap I
> empirically re-litigated "should we abandon crux-2 (7 sorries) for the semantic/TI route (1 sorry)?":
> `peano_not_proves_TI` (Thm 5.6) IS axiom-clean and `peano_not_proves_goodstein_modulo_semantic` is clean
> **modulo the single `DescentSemantic:582` β-wall sorry** — which *looks* one-sorry-from-done. **It is a
> trap.** The lap-45/46 machine-checked finding (`Grz.not_dominated_of_diag_le`) stands: Rathjen §3's
> slow-down is **primrec-only**, a free-`X` (oracle) descent is **not** primrec-dominated, so that `sorry`
> asks for the *impossible* — and `modulo_semantic` is a vestigial theorem built on a FALSE sorry; wiring it
> to the headline would be fraud (free-X-TI ⊢ PRWO is the wrong direction anyway). **The PRWO descent IS
> internally primrec, so crux-2 (Gentzen `PRWO→Con`) is the only honest route.** crux-2's cut-elimination
> is the genuine highest-value target; the lap-97 I∀ eigensubst rewire unblocked its zK validity residuals.
> **NEXT (handoff lap-97, validated):** `ZDerivation_red_zK` replace branches (Crux2Blueprint:206,214) →
> `iord_descent_red` → `foundation_bot_to_Z_empty`/`false_of_ZDerivesEmpty` → wire to headline. **HOUSEKEEPING
> flagged:** `DescentSemantic:582` + `peano_not_proves_goodstein_modulo_semantic` are off-path/built-on-a-
> dead-sorry — candidates for `wip/` (deferred; harmless disclosed sorries, not blocking).

**Kirby–Paris: `𝗣𝗔 ⊬ Goodstein`. ROUTE RESOLVED (lap 45→46) to Rathjen 2014 Cor 3.7 = the original
DIRECTION/Gödel-II plan: `𝗣𝗔⊢γ →(§3, all primrec) 𝗣𝗔⊢PRWO(ε₀) →(Gentzen Thm 2.8(i)) 𝗣𝗔⊢Con(𝗣𝗔)`, then
Gödel II.** The §3 internal pipeline = internal Cor 3.4 (Grzegorczyk `g`-padding, internal level — DEEP,
open) → internal Thm 3.5 (slow α → tight `C(βᵣ)≤r+1` — **COMPLETE lap 47**, `InternalThm35`) → Lemma 3.6
(`nonterminating_internal`, done). The Buchholz free-X `peano_not_proves_TI` (axiom-clean) is a **banked
asset, OFF the headline path** (free-X-TI ⊢ PRWO, wrong direction). **Crux 1 (`γ→PRWO`) LANDED axiom-clean
(lap 57); crux 2 (`PRWO→Con`, Buchholz-Z ordinal analysis arithmetized in IΣ₁) is the sole remaining math
content — the 🟡 active frontier, now sharply localized to `RedSound` (InternalZ.lean): the `iR2`-reduct of
a contradiction derivation must itself be a genuine `ZDerivation` = real internalized cut-elimination.** ·
**Build**: 🟢 green (`lake build GoodsteinPA`, 1325 jobs) · **Updated**: lap 107 (FRESH-MIND REVIEW —
DIRECTION CHANGE: the external-inductive prototype track (`ZInf`/`ZcOK`/`ZcDer`, laps 102→106) is a DEAD
END — `ZInf.allInv` is VACUOUS (kernel-verified one-weakening proof) and external inductives can't carry a
non-standard-code descent; PIVOT to redesigning the Σ₁ engine `red` to find+reduce the lowest cut, the
true crux of `iord_descent_red`; see lap-107 box at top) · earlier lap 104 (FRESH-MIND REVIEW —
direction KEPT; lap-103 endgame packaging CORRECTED by in-kernel certificate: `hinv` is unsatisfiable for
the naive dispatch-shaped `P`, needs Schütte inversion + the Path-C datatype; see lap-104 box) ·
earlier lap 101 (DEEP REFLECTION —
destination/target KEPT; sub-route fork REOPENED, de-risk spike for ω-rule Path C is the next target; see
lap-101 box at top) · earlier lap 98 (FRESH-MIND REVIEW —
direction KEPT; semantic/TI alternative empirically REFUTED as a dead `sorry`) ·
earlier lap 95 (FRESH-MIND REVIEW —
direction KEPT, **Path X CONFIRMED + SHARPENED**: the crux-2 wall is now pinned to ONE surgical fix — gate
`iRK`'s splice on `zTag dᵢ = 4` (NOT a 2–3k-line ω-rule rewrite; O1/O2 are DONE); de-risked in
`wip/InternalZdispatch.lean`; see `ANALYSIS-2026-06-25-lap95-dispatch-fix-not-pivot.md`) · earlier lap 92
(DEEP REFLECTION — ω-rule pivot considered, then lap-92 DECISION favored Path X) · 2026-06-25 · `3bdb3bd`+lap95

> **⭐⭐⭐ Lap-95 FRESH-MIND REVIEW (read FIRST — current).** Re-verified kernel (real `#print axioms`, green
> 1325): headline `peano_not_proves_goodstein = [propext, sorryAx, Classical.choice, Quot.sound]` (0 math
> axioms; `sorryAx` traces the lone math `sorry` = crux-2 = `redSound`), `peano_not_proves_consistency`
> clean. **Direction KEPT, Path X CONFIRMED.** The "Path X vs Path C / 2–3k-line ω-rule pivot" fork is
> DISSOLVED by reading the kernel state: **O2 is DONE** (`ZDerivation_zsubst`, `Zsubst.lean:1855`,
> axiom-clean = the benign criticality-free eigensubst; the lap-78 "substitution wall" was the criticality
> conjunct, dropped when `ZPhi` moved to `zKValidF`), and **O1 is DONE except one leaf** — `ZRegular_red_zK`
> (`Zsubst.lean:1788`) is fully proved *modulo the single hypothesis `hseltag`*. **The entire remaining
> regularity wall = that ONE false hypothesis**: `hseltag` (splice ⟹ `zTag dᵢ = 4`) is FALSE under the
> current `iRK` (the splice fires by default on non-chain selected premises, `not_permIdx_lt_zKseq_zAtom`).
> **Fix = a surgical gate**: splice only when `zTag dᵢ = 4 ∧ ¬ permIdx dᵢ < lh(zKseq dᵢ)` (= dᵢ a critical
> chain); route non-chains to the replace (Buchholz Def 3.2 case 5.2.2). The ω-rule *selection* reading is
> the SOUNDNESS justification, NOT a reason to rebuild a node/`Fixpoint` (a naive ω-node would anyway break
> `Fixpoint.StrongFinite`; the bounded-generator design = `zIall` + the derived benign-subst = what we
> have). **This lap LANDED the gate IN-PLACE (green 1325, axiom-clean):** `iRK` gates the splice on
> `zTag dᵢ = 4` (`iRKDef`/`iRK_defined`/invariants updated); `red_zK_splice` gains `htag`, new
> `red_zK_rep_nonchain`; **`ZRegular_red_zK` is now UNCONDITIONAL** (`hseltag` dropped, `#print axioms =
> [propext, choice, Quot.sound]`) — the lap-94 regularity wall is cleared in-kernel. **NEXT:** the deep
> validity half (`tpReduce` conclusion-reduction for the non-`Rep` replace, lap-90) + `iord_descent_red`.

> **⭐⭐⭐ Lap-92 DEEP REFLECTION (historical — see lap-95 box above).** See `REFLECTION-2026-06-25-lap92.md` (primary
> deliverable). Re-verified kernel (real `#print axioms`, green 1325): headline `[propext, sorryAx, choice,
> Quot.sound]` (0 math axioms), `peano_not_proves_consistency` clean, faithfulness anchor
> `goodsteinSentence_faithful` clean (statement re-audited vs paper — no drift). **Direction KEPT; sub-route
> PIVOT recommended (route C).** The altitude finding: crux-2 `redSound` is the right target, but the
> arithmetized engine (`InternalZ.lean`) was built on Buchholz's **finitary system Z with eigenvariables**,
> and that choice is the direct cause of the wall that has held laps 78–91 (~13 laps). Route A (keep-Π `red`)
> refuted lap-90; route B (`tpReduce` conclusion-reducing reduct, laps 90–91) **still needs validity-preserving
> eigenvariable substitution** (lap-90 lines 127–130/145–148) = the O2 / lap-78 wall, with **no validity-free
> bypass** (lap-90 lines 132–143). **The fix = arithmetize the infinitary ω-rule system** (Buchholz §6 `Z^∞` /
> Schütte `PA_ω`), as the repo's *own meta engine* `Zinfty.lean` already does axiom-clean and as Bryce–Goré's
> complete Coq `Con(PA)` does. In an ω-rule node `∀xF` comes from a premise family `{dₙ ⊢ Γ→F(n)}`; a critical
> cut *selects* `dₙ` (already deriving `Γ→F(n)`) instead of substituting an eigenvariable ⟹ **O1 (freshness),
> O2 (eigen-subst), and route-B's `tpReduce` conclusion-tracking all collapse at once**. Reused unchanged: the
> axiom-clean `iord`/`icmp`/`idg`/`iõ`/ω-tower engine + `Zinfty` as template; recursion on `iord<ε₀` is licensed
> by the PRWO hypothesis itself. Risk (named, honest): the ω-rule's IΣ₁ arithmetization (premise-n as a Σ₁
> recursive notation, Buchholz §6 `Z*`; cut-elim by `iord`-recursion) is new and could have its own wall.
> **NEXT (de-risked): a `wip/InternalZomega.lean` SPIKE** that defines the internal ω-rule ∀-node + its
> critical-cut reduct and *confirms by elaboration* the reduct is substitution-free, BEFORE committing the
> ~2–3k-line pivot. **STOP** investing in finitary `tpReduce`/`Zsubst` eigenvariable substitution.

> **⭐ Lap-89 FRESH-MIND REVIEW (historical — see lap-92 box above).** Re-verified kernel (real `#print axioms`, build
> green 1325): headline `peano_not_proves_goodstein = [propext, sorryAx, choice, Quot.sound]` (**0 math
> axioms**, anti-fraud intact). **Direction KEPT.** ⭐ **KEY UPDATE the lap-88 handoff missed:**
> `peano_not_proves_consistency = [propext, choice, Quot.sound]` — **axiom-clean**. The
> `PA_delta1Definable` "second front" that laps 74/78/81 sweated over (the whole `src/PADelta1.lean`
> campaign) is **resolved UPSTREAM**: Foundation discharged it — `PA_delta1Definable : 𝗣𝗔.Δ₁` is now a
> proven `noncomputable instance` (`Foundation/…/InductionSchemeDelta1.lean:1379`), no longer an axiom.
> ⟹ **the headline endgame is now SINGLE-FRONT**: `goodstein_implies_consistency` (`Reduction.lean:68`,
> the lone `sorry`) = crux-1 (DONE, lap 57) ∘ crux-2. Crux-2 = `redSound` = internalized cut-elimination,
> all three dispatch branches (5.1/5.2.1/5.2.2) now OBJECT-complete (validity + descent + ZDerivation
> co-located, laps 84–88). Remaining = the tag-4 DISPATCH assembly in `iRNextG` + `redSound`/
> `iord_descent_red` + wire `Crux2Blueprint` → `false_of_ZDerivesEmpty` → headline. See
> `HANDOFF-2026-06-25-lap88.md`, `PENDING_WORK.md` lap-88 box.

> **⭐ Lap-86 FRESH-MIND REVIEW (historical — see lap-89 box above).** Re-verified kernel (real `#print axioms`, build
> green 1325): headline `peano_not_proves_goodstein = [propext, sorryAx, choice, Quot.sound]` (**0 math
> axioms**, anti-fraud intact). **Direction KEPT.** Resolved the lap-85 gating question (its NEXT priority
> 2): *does a `ZDerivesEmpty` K-chain always have a critical redex?* **ANSWER: NO** — proved in-kernel
> (`not_zKCritical_red_zK`, axiom-clean) that the critical-only reduct `red (zK s r ds) = iRcritG …` is
> ITSELF a non-critical chain (its `⊥`-half premise is a `K`-chain, `tp = isymRep`, permissible
> everywhere). ⟹ the iterate-descent's `zKCritical` hypothesis (`iord_iR2_iterate_descends`'s `hcrit`) is
> **unsatisfiable after one reduction step**, so the critical-only `red`/`iR2` (Buchholz Def 3.2 case
> **5.1 only**) cannot drive the ε₀-descent on its own. **Plan correction:** lap-85 priority-1 bridge
> `iord (red x) = iord (iR2 x)` is necessary but NOT sufficient (inherits `iR2`'s now-false criticality);
> `red`'s tag-4 must DISPATCH 5.1 / 5.2.1-splice / 5.2.2-replace (descent for each already banked,
> lap-82). The genuinely-new content is the dispatch DEFINITION + `redSound` (validity, `zKValidF`) for
> the 5.2 reducts. See `ANALYSIS-2026-06-25-lap86-criticality-resolved.md`, `PENDING_WORK.md` lap-86 box.

> **⭐ Lap-81 FRESH-MIND REVIEW (read FIRST — current).** Re-verified kernel (real `#print axioms`, build
> green): headline `peano_not_proves_goodstein = [propext, sorryAx, choice, Quot.sound]` (**0 math axioms**,
> anti-fraud intact); `peano_not_proves_consistency = + PA_delta1Definable`; `paMinusDelta1` clean;
> `Thm56.peano_not_proves_TI = + native_decide artifact` (🟢). **Direction KEPT — sound, not stale.** Two
> headline blockers stand: (1) crux 2 (`RedSound` internalized cut-elimination) — DEEP-REFLECTION-blocked
> (lap-78 structural-criticality redesign decision still pending altitude); (2) `PA_delta1Definable` — the
> actively-movable front, well-scoped, advancing lap-over-lap. **Decision: keep driving the Δ₁ thread** (a
> genuine axiom-discharge = CORE work; the operator's literal target is the axiom-free headline, and this is
> the named upstream axiom that's chippable now). **This lap:** PROVED the **criticality crux**
> `not_criticality_aux` (axiom-clean) — the math heart of the `inductionSchemeUnivDelta1` mem_iff:
> `0 < ψ.fvSup → ¬(IsSemiformula ℒₒᵣ (ψ.fvSup-1) ⌜fixitr 0 fvSup ▹ ψ⌝ ∧ shift=self)`, which pins
> `m = fvSup` in the recognizer. Full lap-80 `IsSemiformula.sound` route, now machine-checked, via 6
> new axiom-clean helpers: `subst_eq_subst_of` (formula-subst congruence), `subst_fvarSeq_quote`,
> `fvar?_substs_lt`, `freeVariables_eq_empty_of_shift`, `subst_fvarSeq_le`/`subst_fvarSeq_succ` (the
> last two dodge the `V=ℕ` order diamond by bundling bounds at generic V). NEXT: assemble mem_iff
> (⇐ uses `not_criticality_aux`; ⇒ inversion) + the independent `ch : 𝚫₁.Semisentence 1`. See
> `HANDOFF-2026-06-25-lap81.md`, `PENDING_WORK.md` lap-81 box.

> **⭐⭐⭐ Lap-78 FRESH-MIND REVIEW (historical — see lap-81 box above).** Re-verified kernel (real `#print axioms`,
> build green **1324**): headline `peano_not_proves_goodstein = [propext, sorryAx, choice, Quot.sound]`
> (0 math axioms, anti-fraud intact). **KEY FINDING — the crux-2 rung-2 plan is ARCHITECTURE-BLOCKED, not
> a one-lap freshness add.** `ZDerivation_zsubst` (lap-77, `d ≤ a` form, axiom-clean, banked) cannot be
> generalized to the non-vacuous form rung 2 needs: it **cannot preserve the `zKValid` criticality
> conjunct** (`¬iperm (tp dᵢ) s`, a formula-*inequality*) under numeral substitution, because `fvSubst`
> is non-injective — proven by two explicit counterexamples (CE-1 kills `aNotEigen`-only; CE-2 kills even
> full Buchholz regularity: a substituted numeral `i` coincides with a conclusion term `F(i)`). The
> chain-rule criticality DESIGN is the wall; fix = a deep-reflection decision (recommend "structural
> criticality": track the principal premise by index/rank, not syntactic inequality). See
> `ANALYSIS-2026-06-24-lap78-criticality-substitution-wall.md`. **Pivot:** the independent, mandatory
> `PA_delta1Definable` (Foundation upstream `axiom 𝗣𝗔.Δ₁`; the OTHER headline blocker). Landed
> `paMinusDelta1 : 𝗣𝗔⁻.Δ₁` **axiom-clean** (`Theory.Δ₁.ofFinite`, `𝗣𝗔⁻` finite) + the assembly
> `paDelta1 : 𝗣𝗔.Δ₁` (rfl: `𝗣𝗔 = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`); the whole wall is now isolated to
> `inductionSchemeUnivDelta1 : (InductionScheme ℒₒᵣ Set.univ).Δ₁` (internal `succInd`/`univCl` Δ₁
> recognizer — `src/GoodsteinPA/PADelta1.lean`, one disclosed `sorry` + full construction plan). NOT
> wired to `Reduction.lean` (anti-fraud). Direction KEEP (route sound); the crux-2 *mechanism* needs a
> redesign before rung 2, while `PA_delta1Definable` is chippable in parallel now.

> **⭐⭐⭐ Lap-74 DEEP REFLECTION (historical — see lap-78 box above).** See `REFLECTION-2026-06-24-lap74.md` (primary
> deliverable). Re-verified the kernel (real `#print axioms`, build green **1323**): headline
> `peano_not_proves_goodstein = [propext, sorryAx, choice, Quot.sound]` (**0 math axioms**, anti-fraud
> intact); `goodstein_implies_consistency = + PA_delta1Definable`; faithfulness anchor clean. **Direction
> KEEP — re-validated, not stale; trajectory is monotone forward motion (laps 66→73), not circling.** Three
> altitude sharpenings the grind laps can't make: **(1) crux 2 is genuinely UNAVOIDABLE — *proven* this lap**:
> the banked free-X `peano_not_proves_TI` is the WRONG SHAPE (`γ` can't imply free-`X` TI), the
> specific-instance route still needs Gentzen, and the meta-level monument can't be reused internally — so no
> ε₀-strength-free proof exists; the "off-path" verdict is correct, a future lap must not re-litigate it.
> **(2) lap-70 reduct re-work**: the genuine Option-A reduct re-fits BOTH validity (RedSound) AND its own
> descent (`o(R d)≺o(d)`); the `iord`/ω-tower *assignment* machinery is reusable but the `iR2`/`iCritReduct`
> *definition* + `iord_iR2_iterate_descends` *assembly* are superseded — STOP extending `iR2` infra. **(3)
> `PA_delta1Definable` is the named SECOND FRONT**: still an `axiom` upstream (confirmed), independent of crux
> 2, mandatory for axiom-free, untouched — the biggest non-cut-elim risk to the endpoint. **Highest-value next
> = finish `ZDerivation_zsubst` (rung-1 step 2)** → genuine Ind reduct (rung 2). Direction unchanged; drive
> the RedSound rung ladder.

> **⭐⭐⭐ Lap-71 FRESH-MIND REVIEW (historical — see lap-74 box above).** Re-verified the kernel from real `#print
> axioms`: headline `peano_not_proves_goodstein` = `[propext, sorryAx, choice, Quot.sound]` (**0 math
> axioms**, honest `sorry`, anti-fraud intact); `goodstein_implies_consistency` = that + `PA_delta1Definable`;
> the lap-70 landmark lemmas (`not_zKValid_iCritReduct`, `ZDerivation_iR2_zIall`, `iord_descent_iR2_zK_of_valid`)
> all clean `[propext, choice, Quot.sound]`; build green 1321 jobs. **Direction KEPT — validated, not stale.**
> The crux-2 wall is now correctly localized to ONE obligation, `RedSound` (`InternalZ.lean:4703`): the
> `iR2`-reduct of a `ZDerivesEmpty` derivation must be a genuine `ZDerivation`. Lap 70 **refuted Option B
> in-kernel** (`not_zKValid_iCritReduct`: the ordinal-faithful `iR2` can never preserve `zKValid` — its
> reduct premises are `Rep`-tagged chains, breaking criticality the L3.1 redex finder needs) and **forced
> Option A** (a genuine validity-preserving, cut-formula-shape-dispatched reduct, cross-checked vs Bryce–Goré
> `cut_elim.v`). The ladder (PENDING_WORK lap-70): rung 0.5 = strengthen `ZPhi`'s I∀/Ind disjuncts with the
> premise-sequent + eigenvariable side conditions (so the reduct's threading is provable) → `zsubst`
> (eigenvariable substitution on Z-derivations) → genuine Ind reduct (tag 3, the more tractable wall —
> premises are genuine sub-derivations, not `Rep`) → genuine critical/K reduct (tag 4, the cut-elimination) →
> `RedSound` tag-dispatch. **This lap drives rung 0.5** (`zIndWff` + Δ₁-definability + `ZPhi` wiring), the
> immediate scoped prerequisite. Parallel residual: `PA_delta1Definable` (Foundation upstream axiom, mandatory
> for axiom-free). See `HANDOFF-2026-06-24-lap70.md` + `ANALYSIS-2026-06-24-lap69-redsound-wall.md`.

> **⭐⭐ Lap-62 DEEP REFLECTION (historical).** See `REFLECTION-2026-06-24-lap62.md` (primary deliverable),
> `HARVEST.md` (new), `E-EQ5-ROUTE-FINDING-2026-06-23.md` (judge). **Direction KEEP — trajectory is genuine
> forward motion, not circling** (crux 1 landed lap 57; 58–61 correctly built crux-2's axiom-clean ordinal
> engine; no repeated failed attempts). Re-verified kernel: headline `[propext, sorryAx, choice, Quot.sound]`
> (0 math axioms), `goodsteinSentence_faithful` CLEAN `[propext, choice, Quot.sound]`, `peano_not_proves_TI`
> CLEAN. **Three sharpenings the grind laps couldn't make:**
> 1. **Endpoint HARDENED (operator directive supersedes lap-53).** Trevor 2026-06-23: **axiom-free or
>    abandoned** — no cited `PRWO→Con` axiom on the headline; `PA_delta1Definable` must also be discharged.
>    Lap-53's "honest endpoint = cited eq-5 axiom" is FORBIDDEN. This re-classifies **crux 2 from
>    🟠-generational-cited-axiom → 🟡 project-scale frontier debt that must be fully discharged** — honest
>    because **feasibility is SETTLED**: the Gentzen `Con(PA)` core was machine-checked in **Coq, Feb 2026**
>    (Bryce–Goré, arXiv:2603.00487; judge finishability ~60% multi-month, up from ~35%).
> 2. **C0.5 Foundation→Z bridge is LOAD-BEARING and was unplanned.** `gentzen_descent_of_inconsistent` is
>    fired by `¬𝗣𝗔.Consistent M` (a **Foundation** ⊥-proof) but `iord`/`iR` live on **Buchholz-Z** — nothing
>    converts one to the other (~1k-line milestone = Bryce–Goré's `Peano.v`). Bridge lemma TYPE written
>    (`InternalZ.lean` footer); fork resolved to **(B) keep Buchholz-Z + bridge** (judge-endorsed; matches
>    Bryce–Goré). The `GentzenCon.lean` footer's "arithmetize over Foundation's `Theory.Derivation`" plan is
>    SUPERSEDED.
> 3. **Sequencing: build the OBJECTS before more algebra.** The assignment interior (F1–F4, ω-tower,
>    `idg`/`iõ`/`iord`, C3 templates) is rich, but the objects it operates on don't exist yet: **Fixpoint
>    `ZDerivation`** (so derivations are inductive objects), **`iR`** (C2 reduction), **C0.5 bridge**. The C3
>    templates are conditionals that cannot be instantiated per-rule without them. **Highest-value next =
>    Fixpoint `ZDerivation : V → Prop`** (lap-61 NEXT #1, confirmed), then `iR`, then the bridge.
> **PARALLEL FRONT:** discharge `PA_delta1Definable` (now mandatory). Filed `ON-LINE-REQUEST` for the
> Bryce–Goré source (C0.5 blueprint).

> **⭐ Lap-59 review summary (read first).** Re-verified the kernel from real `#print axioms` (headline
> `peano_not_proves_goodstein` = `[propext, sorryAx, choice, Quot.sound]`, **0 math axioms**, honest
> `sorry`, anti-fraud intact; `goodstein_implies_consistency` = that + `PA_delta1Definable`; build green
> 1318). **Direction VALIDATED + one reprioritization.** Lap 58 started the internal Hessenberg natural
> sum `#` (`wip/InternalNadd.lean`) for Buchholz's `õ` (crux-2 C1). This lap banked the NF + order
> foundations (`isNF_insTerm`, `isNF_inadd`, `insTerm_prepend`, `inadd_zero_right`, `icmp_omega_pow`,
> `inadd_omega_pow`; all `lake env lean` green, axiom-clean). **Finding (acted on):** the lap-58 next-step
> list put `iC (a#b) ≤ iC a + iC b` alongside the order lemmas, but (a) the §4 descent (Buchholz Thm 4.2 /
> Lemma 4.1) consumes the **order** properties of `#`, not the `iC` bound, and (b) `iC_inadd` does **not**
> follow from the naive `insTerm`-fold (the fold over-counts the inserted coefficient against the whole
> accumulator; the true bound needs the NF leading-exponent structure — `ec ≻` rc's exps so the merge only
> hits `b`). So ORDER (strict `#`-monotonicity + commutativity/associativity on ω-power summands) is now
> the prioritized next deep target; `iC_inadd` is deferred (and only matters for C4 bounds, if at all).
> See `PENDING_WORK.md` lap-59. Crux 1 (`seqDescent_dominated`) untouched this lap; still the tractable
> milestone — see prior lap-56 box.

> **⭐ Lap-56 review summary (read this first).** Two crux-1 architecture findings, both acted on
> (`wip/GentzenCon.lean`, verified `lake env lean` green; memory `prwo-transparent-icmp-not-opaque-precphi`).
> **(1) Opacity DISSOLVED.** Lap-55 built `prwoInstance` on the OPAQUE `precφ` (`codeOfREPred₂`, std-model-
> only spec) — re-creating wall-B opacity in nonstandard `M`. Fix (mirrors lap-36): rebuilt on the
> TRANSPARENT `InternalONote.icmp` via `prec_internal := “z y. ∃ c, !icmpDef c z y ∧ c = 0”`
> (`eval_prec_internal : M⊧prec_internal[z,y] ↔ icmp z y = 0`, every `M⊧IΣ₁`). ⟹ the **natCode↔NF order
> bridge (lap-55's "new sub-target") DISSOLVES** — `nonterminating_of_seq_descent`'s hyp IS already the
> `icmp`-descent the girder consumes; PRWO now shares `igoodstein`'s coding; `prwoInstance_faithful` is a
> clean corollary that SHED its F-φ native_decide artifact. `eval_prec_internal`/`prwoInstance_models_iff`/
> `_faithful` axiom-clean; `goodstein_implies_prwo` clean modulo the lone bridge sorry. **(2) Over-generality
> (OPEN, the real remaining content).** `nonterminating_of_seq_descent` as stated (arbitrary `seq`, NO
> domination hyp) is **UNPROVABLE on the standard-level girder** (`F_diag_not_dominated`): proving it for
> arbitrary seq needs the internal-Ackermann wall lap 50 showed the headline avoids. **Fix next lap:** thread
> a standard-level domination certificate (Cor-3.4 slowdown inputs from `seq`), discharge it at
> `gentzenDescentφ`, then it reduces to `crux1_internal_run_of_width_dom` sorry-free. Crux-2 eq-(5) still 🟠.
> **(3) Seam wired (also this lap).** Promoted `StdCor34` → `src/` (sorry-free, axiom-free; build 1316).
> Added `SeqDominated` (the certificate) + `nonterminating_of_dominated` (**axiom-clean** — the
> certificate→girder seam now type-checks end-to-end) so `nonterminating_of_seq_descent` is **PROVED**; the
> lone remaining crux-1 sorry is now the sharper `seqDescent_dominated` (build `SeqDominated` from the
> `seq`-descent = the Cor-3.4 construction). THE next deep target.

> **⭐ Lap-53 honest-endpoint summary (read this first).** Route A is CORRECT (re-derived from the
> mathematics this lap: Goodstein⟹PRWO, NOT free-X-TI — the §3 slow-down is primrec-only). The two cruxes
> have **asymmetric feasibility**: **crux 1** (`γ→PRWO`) is 🟡 TRACTABLE (~80% built, standard-level, a few
> laps to assembly) — KEEP DRIVING IT; **crux 2** (`PRWO→Con`, Gentzen ord/R/eq-5 arithmetized in PA) is 🟠
> GENERATIONAL with **no shortcut** (confirmed: Foundation's Hauptsatz is meta-level, no arithmetized
> ordinal analysis exists upstream) — its `wip/GentzenCon.lean` scaffold already isolates it to the single
> cited eq-(5) `ord_R_descends` axiom; chip only opportunistically. **The realistic, valuable, honest
> endpoint = crux-1 fully built + crux-2 reduced to cited Gentzen eq-(5) + `PA_delta1Definable` upstream**,
> i.e. headline `#print axioms` best-case `[propext, choice, Quot.sound, PA_delta1Definable]` (NOT the
> strict trust base DIRECTION rule #1 names — INHERENT to Gödel II; needs operator reconciliation, rec:
> accept the one disclosed upstream axiom). See `REFLECTION-2026-06-23-lap53.md`.

## ⭐ Lap-44 (DEEP REFLECTION) — kernel re-verified, slow-down re-grounded; the wall's `sorry` is framed on a DEAD path
**Direction: KEEP** (Buchholz §5 girder DONE+axiom-clean; E = one semantic wall = Rathjen §3 slow-down in `M`).
Real `#print axioms` reconfirmed: headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms);
`peano_not_proves_TI` clean; whole `…_modulo_semantic` chain = trust-base + 1 🟢 native_decide + **1
`sorryAx`** (the wall). **Two altitude findings the grind laps couldn't see** (`REFLECTION-2026-06-23-lap44.md`):
- **(A) The literal wall `sorry` (`DescentSemantic.lean:574`) routes through the DEAD 𝚺₁ path** (`hbound` +
  `DescentArith.nonterminating_internal`, demanding `𝚺₁-Function₁ b`). But `b` is built from the
  **X-definable** descent, so it is genuinely **X-dependent** ⟹ the `hbound` 𝚺₁ shape is **unachievable
  (FALSE in general)**, not merely hard. The fix is already in-file: **`nonterminating_of_xDescent`** (lap
  41, `lx_succ_induction`) reduces the wall to the HONEST obligation *produce the slowed code sequence
  `β : M → M`* (NF, `iCanon (k+1)`, `icmp`-descent, LX-definable run-comparison). **Highest-value next =
  rewire the wall to it.**
- **(B) Transcription caution (Rathjen uses LENGTH `|·|`; repo collapses onto `C`).** Per the PDF: Lemma
  3.3(2)/Cor 3.4 bound `|g|`/`|αᵢ| ≤ K·(i+1)`; the absolute **`C(βᵣ) ≤ r+1` is a SEPARATE stage (Thm 3.5)**
  (built faithfully in `DescentCore.C_betaTail_le` via `C_omega_mul_le`). `Grzegorczyk.lean` works with **C
  throughout** (C-based widths) — self-consistent on paper but the repo's own variant, **UNVERIFIED until
  the Cor 3.4 assembly typechecks** ⟹ finish the ℕ-template assembly (de-risk) before M-internalizing.
**Trajectory verdict:** laps 30→43 are genuine forward motion (real, kernel-verified substrate toward the
one deep wall), NOT circling. Endpoint is a COMPLETE axiom-clean Kirby–Paris — 🟡 project-scale, finishable.

## ⭐ Lap-42 (REVIEW) — the lap-41 "lone wall" `IterPrefix_lxDef` DISCHARGED; descent sequence is unconditional
**Done:** `IterPrefix_lxDef` + `minClause_lxDef` (`DescentConstruction.lean`, axiom-clean, green 1308).
The **membership-form trick** (`isDescent_iff_mem` — the `X`-atom on a *bound* variable, not a `znth`-term)
that lap 35 used for the `Mlt`-descent applies verbatim to lap-41's **`descentR`** route, so all four
`IterPrefix` clauses are binary-`LX`-definable (only the `descentR` minimality `∀ z<x', ¬(Mlt f z x ∧ ¬MX z)`,
via Foundation `ballLT`, was new). ⟹ **`descent_iterate_seq_total : ∀ k:M, IterPrefix hM f a₀ k` is
UNCONDITIONAL** (the canonical `Mlt`-descent prefix exists at every length, hypothesis-free). Lap 41
over-rated this as "genuine multi-lap infra"; it was one membership-form clause.
**Fresh-mind course-correction (recorded in `PENDING_WORK` lap-42):** the prior `hbound` decomposition
**under-specified slowness** — it assumed the extracted descent `α` already has `iC(αₖ)≤K(k+1)`, but a
`descentR`-least step has uncontrolled `C`. Rathjen gets the bound only via **Cor 3.4** (Grzegorczyk
`g`-padding, Lemma 3.3), which is **NOT started** and is now the genuine remaining crux; the lap-41
`InternalONote` toolkit is the *Thm 3.5* reindex arithmetic, downstream of Cor 3.4. Also flagged: the
`hbound` `sorry` still carries the unachievable `𝚺₁-Function₁ b` shape (b is `X`-dependent) — refactor
`hCD` through lap-41's `nonterminating_of_xDescent` when β lands.

## ⭐ Lap-36 (DEEP REFLECTION + WALL B DISSOLVED) — `goodsteinSentence` refactored transparent; `hB` discharged
**Done after the synthesis:** refactored `goodsteinSentence` to the transparent `“∀ m, ∃ N, !igoodsteinDef
0 m N”` (`Encoding.lean`), re-proved `Bridge.goodsteinSentence_faithful` axiom-**clean** with the IDENTICAL
locked RHS, and **closed `hB`** (`DescentSemantic.lean:419`) — `hgood` lifts to `M`'s reduct
(`reduct_eq_standardModel`), evals to `∀ m ∃ N, igoodstein m N = 0`, instantiate at `m₀`. Real `#print
axioms`: `goodsteinSentence_faithful` = `[propext, choice, Quot.sound]`; the chain's lone `sorryAx` is now
**only `hCD`**. `ON-LINE-REQUEST` archived (wall B moot). **Two walls → one; the only literature gate is
gone, the remaining path is entirely offline.** The synthesis that motivated this:

Altitude pass on the stronger model. Real `#print axioms` reconfirmed: the **entire ordinal-analysis girder
is done and axiom-clean** (`Thm56.peano_not_proves_TI` = trust-base + 1 🟢 native_decide), the headline is
an honest `sorry` (0 math axioms), and the would-be-headline `…_modulo_semantic` carries exactly **one**
`sorryAx` from `no_min_descent_absurd_of_goodstein` — which splits into `hCD` (wall C+D, descent⟹run-never-
dies) and `hB` (wall B, the opaque code↔run bridge). **Finding:** wall B exists ONLY because
`goodsteinSentence = ∀⁰ (codeOfREPred goodsteinTerminates)` is Foundation's **opaque** `Classical.epsilon`
r.e. blob — and every lap since 24 treated that blob as a *fixed* target and tried to *bridge to it*
(literature-gated `ON-LINE-REQUEST`). But `goodsteinSentence` is **not** in the LOCK list, and
`Encoding.lean`'s own docstring (lines 35–39) **explicitly sanctions** refactoring it to a transparent form,
"gated by matching this bridge's spec, so faithfulness can never silently regress." **The course change:
redefine `goodsteinSentence` as the transparent Π₂ sentence built from the repo's own
`igoodsteinDef : 𝚺₁.Semisentence 3`** (`InternalGoodstein`), re-prove `goodsteinSentence_faithful` (identical
locked RHS) via `igoodstein_nat`+`igoodstein_defined` — then `hB` falls out of `hgood` directly and wall B
**dissolves into a mechanical Foundation eval**, removing the project's only literature gate. De-risked this
lap: `igoodsteinDef`/`igoodstein_defined`/`igoodstein_nat` all exist; the `Internal*` chain is `Encoding`-free
(no import cycle); `models_lMap_goodstein` is form-independent; complexity (Π₂) unchanged. After the refactor
the lone genuine wall is **C+D (`hCD`)** — Rathjen §3 slow-down internalized in `M`; its ONote kernel
(`DescentCore`) is built, fully offline. See `REFLECTION-2026-06-23-lap36.md`. Build green 1306 jobs.

## ✅ Lap-30 (review) — STRATEGIC REDIRECT: the E wall collapses to ONE semantic lemma via completeness
Fresh-mind pass found the lap-27 "Route B = hand-build a `paLX` sequent-calculus derivation of `TI_≺(X)`"
plan (literature-gated, `ON-LINE-REQUEST.md`) is **not the cleanest route**. Foundation's **first-order
completeness theorem** (`Derivation.completeness_of_encodable`, general FO, on disk) produces
`(paLX : Schema) ⟹ [TI prec]` from a single *semantic* premise. So `Thm56.DescentE` — and hence the whole
headline — **reduces to ONE model-theoretic lemma** `paLX_models_TI_of_PA_provable` (`src/DescentSemantic.lean`,
NEW): *under `𝗣𝗔 ⊢ goodsteinSentence`, every model `M ⊧ paLX` satisfies `TI prec`*. This is Rathjen §3
carried out **inside `M`** (the free predicate `X` is `M`'s interpretation; inequality (6)'s induction is
`M ⊧ InductionScheme LX`). Three wins: (i) **resolves the free-`X` obstruction** (work in models of `paLX`,
not `𝗜𝚺₁` — `X` present throughout; completeness does the syntactic lift), (ii) **no literature gate**
(standard model theory, not a bespoke sequent shape), (iii) **reuses the lap-26 substrate**
(`igoodstein`/`ibump` live in `M`'s `ℒₒᵣ`-reduct; `DescentCore.ineq6_step` is the kernel). `descentE :
Thm56.DescentE` and `peano_not_proves_goodstein_modulo_semantic : 𝗣𝗔 ⊬ goodsteinSentence` are **proved
modulo the one disclosed `sorry`**; **real `#print axioms` on both = `[propext, sorryAx, choice, Quot.sound,
ONoteComp…native_decide.ax_1_5]`** — the moment the semantic lemma is real, the headline is axiom-clean
(NO `PA_delta1Definable`, NO custom axiom). `Statement.lean` headline `sorry` untouched (anti-fraud). Built
`LX.Encodable`. The remaining wall is now a single, decomposable semantic obligation — see `DESCENT-PLAN §5`.

## ✅ Lap-28 — F-φ DISCHARGED: Thm 5.6 is now FULLY axiom-clean; ONE wall left (E-core)
Completed the v4.28→v4.31 port of Aristotle's `rePred_ltPull_natCode` (CNF comparison is r.e./computable)
and **wired it into the headline route**, turning the lone F-φ math axiom into a machine-checked theorem.
`src/GoodsteinPA/ONoteComp.lean` (promoted from `wip/`, green, sorry-free) supplies the `Computable`
proof of CNF comparison via a structural strong recursion. `SeamDefinability.rePred_ltPull_natCode` is
now a `theorem` (chains ONoteComp), not an `axiom`. **Real `#print axioms peano_not_proves_TI` =
`[propext, Classical.choice, Quot.sound, ONoteComp.cmpStep_spec._native.native_decide.ax_1_5]`** — the
F-φ math axiom is GONE; only one 🟢 `native_decide` finite base-case witness remains (acceptable per
doctrine). Port fixes over the lap-27 wip: rewrote the convert-heavy `Computable` proofs
(`computable_cmpStep`/`_nfTB`/`_nthNF`) as direct combinator terms (added `primrec_thenNat`/`_cmpNat`/
`_cmpNV`); reproved `enc_strictMono` structurally via the `Nat.Subtype.ofNat` enumeration + `ofEquiv_ofNat`
(the v4.31-drift item); replaced the slow `nlinarith` index bound in `cmpStep_spec` with `pair_lt_pair`+
`omega`; `import Mathlib.Tactic.Linarith`. **The project now has exactly ONE wall: E-core (Route-B
form).** Headline `peano_not_proves_goodstein` still an honest `sorry` (anti-fraud intact). Port detail:
`wip/aristotle-fphi/PORT-STATUS.md`.

## ✅ Lap-27 (DEEP REFLECTION) — F-φ SOLVED on Aristotle; back-end choice DECIDED (Route B); one wall left
Altitude pass. **Two state changes.** (1) **F-φ is SOLVED:** the Aristotle job `aris_onotecmp` returned
COMPLETE — `rePred_ltPull_natCode` proved (622-line `ONoteComp.lean`, no `sorry`, no new axioms beyond
2 `native_decide`). Verified faithful here: its final statement is *verbatim* ours and it uses **our**
`natCode := (Denumerable.eqv NONote).symm`. Caveat: proved on `v4.28.0` vs our `v4.31.0` ⟹ a mechanical
cross-version **port** is pending (stashed `wip/aristotle-fphi/`). F-φ is now "proof in hand," not "open."
(2) **COURSE CORRECTION — commit to Route B; stop deferring the back-end.** The lap 25–26 internal-V
machinery (`DescentArith.ineq6_internal` via `sigma1_pos_succ_induction`) builds **Route A's** front-half
(`𝗣𝗔 ⊢ goodstein → 𝗣𝗔 ⊢ PRWO(ε₀)`, X-free), which **cannot** feed the built, axiom-clean **Route B**
back-end `peano_not_proves_TI` (the free-`X` obstruction the team itself flagged in the lap-24
correction: `𝗣𝗔 ⊢ PRWO`/primrec can't refute the X-definable counterexample to `TI prec`; E-lift can't
make the free `X` either). Route A carries `PA_delta1Definable` (🟡), which the anti-fraud rule forbids
on the headline — so Route A can never finish cleanly. **Decision: Route B is primary and committed.**
The lap-26 *arithmetic substrate* (`InternalPow/Digits/Log/Bump/Goodstein`+`InternalBridge`) is **kept**
(reused as `LX`-formula builders for the Route-B paLX construction, ~70% transfers); only the
`DescentArith` `sigma1_pos_succ_induction` *induction wrapper* is Route-A-flavored and off the
clean-headline path. **Highest-value next = port F-φ** (proof in hand ⟹ discharges a whole wall),
collapsing the project to a **single** wall: **E-core(b), Route-B form** (inequality (6) as an
`InductionScheme LX` step on the X-definable descent inside paLX). Faithfulness audit of the headline
reduction (`Thm56`/`Seam`) clean — no transcription drift. Headline still honest `sorry`. See
`REFLECTION-2026-06-23.md`.

## ✅ Lap-24 (review) — direction re-validated against the real kernel; **two walls left: E-core + F-φ**
Fresh-mind pass. Confirmed via real `#print axioms` (not the stale lap-21 ledger): **D' is fully
discharged** (lap 22, `embed_TI_bounded` now chains `EmbeddingBound.embedC_LX_bdd`, no `sorryAx`), and
**`peano_not_proves_TI` carries exactly `[propext, choice, Quot.sound, rePred_ltPull_natCode]`** — the
ONE remaining math axiom on the entire Thm 5.6 route is **F-φ** (on Aristotle, `aris_onotecmp`,
RUNNING). The X-free **E-lift** is done (lap 23, axiom-clean) and the first **E-core** semantic brick
(`evalNat` order-reflection, Rathjen 2.3(iii)) is clean. The single remaining girder to the headline
is **E** = `DescentE` (Goodstein ⟹ `TI(ε₀)` inside PA); its deep content is **E-core** (Rathjen §3
"slowing-down" + arithmetization), since E-lift alone does not reach the X-mentioning `TI prec`. Walls
are now **E-core + F-φ** (was E + F-φ + D'). Direction (Buchholz Boundedness route, attack E-core)
**reaffirmed**. `aris_emcong` job was CANCELED (its target `provable_em_cong_gen` is already proved —
nothing to harvest). Headline `peano_not_proves_goodstein` still an honest `sorry` (anti-fraud intact).

## ✅ Lap-21 (review) — Thm 5.6 ASSEMBLED into one theorem + a hidden gap (D') surfaced
`src/GoodsteinPA/Thm56.lean` (NEW) **assembles the entire Buchholz §5 girder** into the single
headline-route theorem **`peano_not_proves_TI : IsEmpty (Derivation2 paLX {TI prec})`** (Gentzen 1943
sharpness, `𝗣𝗔 ⊬ TI_≺(X)`), and reduces the headline to ONE wall **E** via
`peano_not_proves_goodstein_of_descent (hE : DescentE) : 𝗣𝗔 ⊬ ↑goodsteinSentence`. The chain (all
machine-checked): C₂ `embedC_LX`+`hax_paLX` → collapse the assignment image via `asgX_TI_fix` (`TI prec`
is fvar-free, `prec = lMap (emb precφ)`, `precφ` a `Semisentence`) → C₁+D `orderType_le_of_TIprovable` →
F `seam.ge`; the contradiction is `ε₀ ≤ ‖≺‖ ≤ 2^(ω_c^α) < ε₀`. `#print axioms peano_not_proves_TI =
[propext, choice, Quot.sound, sorryAx, rePred_ltPull_natCode]`. Headline untouched (anti-fraud intact).

**⚠️ Fresh-mind review finding — D' is a real, previously-unflagged gap.** The lap-20 handoff claimed
"Thm 5.6 axiom-clean modulo E+F". That is **incomplete**: the contradiction needs the embedded ordinal
`α < ε₀`, but `embedC_LX` only gives `∃ α` (no bound). `α < ε₀` is *the* Gentzen content — a **finite**
PA-proof embeds to a `Z∞`-proof of height `< ε₀` (PA cannot certify heights up to ε₀ itself). Isolated
as the disclosed `sorry` **`embed_TI_bounded`** (D'). It is **tractable, Foundation-light, no literature**:
strengthen `embedC_LX_gen`/`hax_paLX` to the *uniform* conclusion `∃ c, ∃ B<ε₀, ∀ e, ∃ α≤B, PXFc α c …`
(every builder bumps `B` by `+1`/`max+1`/`sup+1`, all `<ε₀`; the ω-rule closes because the IH's `B` is
*outside* `∀ e`, so the family is uniformly `≤B`). **The walls are now E + F-φ + D'** (was E + F-φ).

## ✅ Lap-19 — F's ORDER-TYPE WALL CLOSED (axiom-clean) — the dominant campaign risk is down
The order-type half of **F** (`src/GoodsteinPA/Epsilon0Complete.lean`, all `#print axioms`-clean) is now
machine-checked end-to-end — this is the piece flagged across laps 12-19 as "the dominant risk / the real
F girder mathlib LACKS":
- **`exists_NF_repr_eq`** : `∀ o<ε₀, ∃ x:ONote, x.NF ∧ x.repr=o` — ε₀-completeness of CNF notations (the
  surjectivity mathlib omits), via the standard CNF recursion (`WellFoundedLT.induction`).
- **`repr_lt_epsilon0`** / **`range_NONote_repr`** : the embedding direction + `range NONote.repr = Iio ε₀`.
- **`rk_ltPull_eq_repr`** (= the seam-advice `note_rank_eq_repr`) + **`epsilon0_le_orderType_ltPull`** :
  `ε₀ ≤ orderType (ltPull e)` for ANY coding `e : ℕ ≃ NONote` (no Iio-sup / universe bump — straight to ℕ).
- **`natCode`** (`Encodable ONote` + `Infinite`/`Denumerable NONote`) + **`epsilon0_le_orderType_natCode`** :
  a fully concrete, hypothesis-free `ε₀ ≤ orderType` witness = the `Seam.ge` field.
**F now reduces to one Foundation-side wire-up:** the `ℒₒᵣ` formula `φ` (`codeOfREPred₂`) defining `natCode`'s
order, then `Seam` instantiates (`Seam.ge := epsilon0_le_orderType_natCode`). The order-type *math* is done.

## ⏭️ Open obligations (lap 19 end) — Thm 5.6 is ONE glue lemma from axiom-clean; remaining walls E + F-φ
The **entire machine from D back is now machine-checked + `#print axioms`-clean** (lap 17): Boundedness
(Thm 5.4) + corollary B, **C₁** `PXFc.cutElim`→cr0, **D** `orderType_le_of_TIprovable`, **C₂-structural**
`embedC_LX_gen`, M4 `embedC`, M5 `cutElim`. The single open sorry below the headline (besides the locked
headline + off-path Route-A) is **C₂ glue** `hax_paLX`'s X-induction case (`EmbeddingX.lean:705`, "pure
integration", recipe inlined) — closing it makes **Thm 5.6 (`PA ⊬ TI(ε₀)`)** axiom-clean modulo E+F.
The remaining campaign walls are **E** (Goodstein⟹TI_≺(X)) and **F** (arithmetization seam, `‖≺‖=ε₀` +
discharge `hprec`/`hprecXPos`). **Reflection finding (lap 18, see PENDING_WORK top):** F's order-type half =
**ε₀-completeness of CNF notations** (`∀ o<ε₀, ∃ x:ONote, NF x ∧ repr x=o`), which **mathlib LACKS** (it has
only the order-*embedding* `NONote↪ε₀`, not surjectivity) — it is the real F girder, ~1–3 laps, and being
pure mathlib ordinal arithmetic it is **Aristotle-eligible** (the one piece with no Foundation dependency).
E **pins which `≺` F may use** (co-design). See newest `HANDOFF`.

## Where it stands
**(lap-161 DEEP REFLECTION — CURRENT read.)** Build green **1326** (exit 0); re-verified in-kernel (real
`#print axioms`): headline `peano_not_proves_goodstein` `[propext, sorryAx, choice, Quot.sound]` (0 math axioms,
bare-sorry); `peano_not_proves_consistency` + `goodsteinSentence_faithful` `[propext, choice, Quot.sound]` (clean);
`false_of_ZDerivesEmpty` `[propext, sorryAx, choice, Quot.sound]` (0 math axioms, 6 live sorries) — no drift. Single
open girder being worked = crux-2 (`false_of_ZDerivesEmpty`, IΣ₁-internal Gentzen termination, M1b-term). **The
{3,4}-producer cut-reduction — the deep core of crux-2 (Buchholz Thm 2.1) — is now CLOSED in-kernel** (laps 158-160:
`repProducerClose` via `certReplace_of_premise_cert` + general IH, consumed in the live dispatch `Crux2Blueprint:3578-3581`).
The lap-158 directive that called it "the irreducible open frontier" was STALE: lap-158's own design spike (`9ac1bf3`)
refuted the "outer degree-induction" hypothesis (the producer closes by code-induction with LOCAL per-flatten degree
headroom). **The open `residual` (:3451) / `axMajorResidual` (:3735) now hold ONLY the STRUCTURAL escape set:** (i) ⊥-exit
ex-falso (`⊥∈Γ ⟹ Γ→C`, needs an internal ⊥-elim/weakening lemma — the one genuinely-new piece), (ii) C-exit R-intro
replay, (iii) tag-5/6 thread-escape (shared). The six live sorries are NOT independent: the ex-falso lemma + the anySucc
port collapses FOUR of them (`residual` → noRedex_anySucc leaf → thin-wrap `genReduct_botSucc` → `axMajorResidual` +
`descent_step_K_noncrit_axMajor`); gDef (:4309) is the separable fifth. NEXT = build the ex-falso/weakening lemma, close
`residual`. **ALTITUDE CAUTION (binding):** a sorry-free `false_of_ZDerivesEmpty` is NOT the headline —
`goodstein_implies_consistency` (`Reduction.lean:68`) is a bare sorry, NOT YET wired to `false_of_ZDerivesEmpty`; the
M2/M4 embedding bridge (PA-proof → `ZDerivesEmptyR`) is ~0% built; girder #1 (γ→PRWO) is partly built. "Only the crux
left" ≠ "almost done." See `DIRECTION.md` CURRENT DIRECTIVE (lap-161), `REFLECTION-2026-06-27-lap161.md`.

**(lap-158 FRESH-MIND REVIEW — historical read.)** Build green **1326**; re-verified in-kernel (real
`#print axioms`) the headline + faithfulness anchors (`peano_not_proves_goodstein` `[propext, sorryAx, choice,
Quot.sound]` 0 math axioms; `goodsteinSentence_faithful` + `peano_not_proves_consistency` `[propext, choice,
Quot.sound]` clean; `false_of_ZDerivesEmpty` `[propext, sorryAx, choice, Quot.sound]`) — no drift. Single open
obligation = crux-2 (IΣ₁-internal Gentzen termination, M1b-term). lap-155's **SUCCEDENT-THREADING COLLAPSE**
mandate is DONE + EXHAUSTED: lap 155 (tag-5 sub-case (a) + 2 reusable ordinal lemmas), lap 156 (tag-6 sub-case
(a) + zAxNeg-producer close + the reusable `leastSucc_in_ant_or_nonleaf` general-Γ collapse), lap 157
(`climb_to_rep_producer` PROVEN axiom-clean → the tag-5 `zAxAll` producer collapses to {3,4,6}/escape). **Every
THREADABLE/closeable sub-case of `axMajorResidual` (`Crux2Blueprint:3417`) is now closed** — the lap-155
"test the collapse to exhaustion BEFORE the general route" gate is MET. **This lap's call: the residual is now
the IRREDUCIBLE {3,4}-producer cut-reduction = Buchholz Thm 2.1 general cut-elimination (the heart of crux-2),
NOW UN-FORBIDDEN.** `axMajorResidual` is reached ONLY for a NON-LEAF `Rep` producer (`zInd` tag-3 / sub-`zK`
tag-4) that genuinely PRODUCES the cut formula — un-threadable (laps 155-157) AND un-reducible by a same-degree
`õ`-drop (REFUTED in-kernel lap 157: `irk(cut)+1 ≤ idg` not derivable). Two shapes: (i) tag-5 + the climb →
the cut formula is `^∀^k⊥`, a ∀-TOWER over the CLOSED matrix `⊥` (dominant); (ii) tag-6 → arbitrary `p'`. The
fix must drop the DEGREE (`idg`), reusing the `genReduct_chain_hasRedex` degree-drop engine. MANDATE = a focused
DESIGN SPIKE first (wip/, lap-101/132-style) pinning the generalized statement — OUTER induction on the NAT
`idg` (kosher, unlike `iord`) + INNER code-induction, eliminate highest-rank cuts first (= the missing
headroom), generalize `genReduct_botSucc` off `seqSucc=⊥` to general `C` reusing the same-end-sequent
`certReplace` splice; explore the cheap `^∀⊥→⊥` vacuous-instantiation inversion for shape (i) but confirm it
beats the degree-general route before committing — THEN port to src as named sub-`sorry`s. ALTITUDE CAUTION: M2
(Foundation→Z bridge) ~0% built + crux-entangled — "only the crux is left" ≠ "almost done." See `DIRECTION.md`
CURRENT DIRECTIVE (lap-158), `PENDING_WORK.md` (lap-158 top), `HANDOFF-2026-06-27-lap157.md`.

**(lap-143 DEEP REFLECTION — historical read.)** Build green **1326**; headline honest `sorry` (real in-kernel
`[propext, sorryAx, choice, Quot.sound]`, 0 math axioms; `goodsteinSentence_faithful`/`peano_not_proves_consistency`
clean; statement re-audited — no drift). Single open obligation = crux-2 (the IΣ₁-internal cut-elimination
termination). **This lap's call: KEEP the lap-132 existence-form pivot, but FINISH it.** The pivot frees the
endgame to witness `ZDerivesEmptyR_descent_step`'s bare `∃ d'` with any genuine reduct — but laps 141-142
regressed to witnessing with `red`, so the live `false_of_ZDerivesEmpty` path still routes soundness through the
FALSE/incomplete `redSoundGen` (:1471 → kernel-FALSE `zKValidF_iIndReduct_of_zInd` :80 + open zK :1508 +
kernel-FALSE `ZDerivation_red_zK_crit` :1108). The genuine replacement `ZDerivation_iRKcCrit_critical_all` (:1847)
is banked but UNWIRED. **NEXT:** derive `ZSeqAnt_iRKcCrit`; split `descent_step_K_critical` into ∀ (wire `iRKcCrit`,
red-free) + ¬ (named `redexJ≤j0` sorry); re-witness the Ind branch with `iIndReductSeqG`. The DEAD `red`-soundness
sorries (:80/:1108/:1211/:1384/:1471) then go off-path → `wip/`. See `REFLECTION-2026-06-26-lap143.md`, `DIRECTION.md`.

**(lap-132 DEEP REFLECTION — historical read.)** Build green **1326**; headline honest `sorry` (real in-kernel
`#print axioms = [propext, sorryAx, choice, Quot.sound]`, 0 math axioms; girder = same lone `sorryAx`;
`goodsteinSentence_faithful` + `peano_not_proves_consistency` axiom-clean). Statement re-audited vs source —
no drift. Single open obligation = `goodstein_implies_consistency` = crux-1 (DONE) ∘ crux-2. Diagnosis of
crux-2 is converged and correct (the `red`-engine on the ⊥-orbit). **This lap's call: the SELECTION/STALL
sub-goal that has consumed laps 120→131 is an artifact of the *fixed-deterministic-engine* formulation.**
Reframing the endgame iteration to `redLeast` (Σ₁ least descending reduct) makes "fixpoint ⟹ cut-free"
definitional via a single existence lemma (E), obviating the permIdx-selection campaign and reusing the banked
soundness (laps 112-119), invariant folds (`zReg`/`zFresh`/`seqAntSeq`), and per-reduct descent lemmas. **NEXT
(course-test, mirror lap-101):** a `wip/ExistenceEndgame.lean` spike — `redLeast` + (E) + the existence-form
`false_of_ZDerivesEmpty`. Decisive either way. See `REFLECTION-2026-06-26-lap132.md`, `NEXT_STEPS.md`.

**(lap-120 DEEP REFLECTION — historical read.)** Build green **1326**; headline honest `sorry` (real in-kernel
`#print axioms = [propext, sorryAx, choice, Quot.sound]`, 0 math axioms; girder = same; `peano_not_proves_consistency`
clean). Statement re-audited vs paper — no drift. Single open obligation = `goodstein_implies_consistency` =
crux-1 (DONE) ∘ crux-2. **The inversion is solved; the genuine open crux is the SELECTION/STALL defect.** Laps
112–119 PROVED the critical-cut inversion soundness on both polarities (`iRcritG`/`critReductCorr` ∀,
`iRcritGNeg` ¬, Buchholz §5) — real progress on reduct SOUNDNESS. But the endgame `false_of_ZDerivesEmpty`
(`Crux2Blueprint:1144`, bare sorry) cannot close: `red` STALLS when `permIdx` selects an atom/`zAx1` premise
(`iperm isymRep` unconditionally true), so a tag-4 K-node becomes a `red`-FIXPOINT that is not cut-free. The
lap-111 disjunctive `iord_descent_red` did not FIX this — it RELOCATED it into the unbuilt
`false_of_ZDerivesEmpty` (stall branches close `Or.inl`). Same defect as laps 104/107, still open. **NEXT
(course correction):** confront **(A)** `red w = w ∧ ZDerivesEmptyR w ⟹ False` (vacuity-of-the-stall first;
probe `ZRegular`); then the swap → `redSound`; then (C) `gentzenDescentφ` Σ₁ realization + assemble M3. See
`REFLECTION-2026-06-26-lap120.md`, `NEXT_STEPS.md`.

**(lap-111 DEEP REFLECTION — historical read.)** Build green **1326**; headline honest `sorry` (real in-kernel
`#print axioms = [propext, sorryAx, Classical.choice, Quot.sound]`, 0 math axioms; `goodstein_implies_consistency`
= same lone `sorryAx`; `peano_not_proves_consistency` + `not_proves_of_implies_consistency` + faithfulness
anchor all axiom-clean). Statement re-audited vs paper — no drift. Single open obligation =
`goodstein_implies_consistency` = crux-1 (γ→PRWO, DONE lap 57) ∘ **crux-2** (PRWO→Con, IΣ₁-internal Gentzen
ordinal analysis). **Direction KEPT; one structural lever surfaced.** crux-2 lives in the Σ₁ engine `red`/`iord`
(load-bearing, re-confirmed lap 107); its remaining surface is `iord_descent_red` (descent, ~80% done),
`ZDerivation_red_zK_crit` (critical-case soundness = the ∀/¬-inversion, ≈0% done), `false_of_ZDerivesEmpty`
(M3 PRWO-plumbing), `foundation_bot_to_Z_empty` (M2 embedding, ~1k lines). The descent side has soaked up the
laps while the inversion (the genuine cut-elimination content, prize) sits untouched — its only attempt
(external `ZInf.allInv`) was killed VACUOUS at lap 107. The `iord_descent_red` fixpoint branches
(atom/axAll/axNeg-selected `red d = d` + chain-REPLACE IH false-at-fixpoint) are a SELECTION bug, not descent
gaps. **NEXT (synthesis call):** (1) reformulate `iord_descent_red` → disjunctive `red d = d ∨ iord ≺` and
`false_of_ZDerivesEmpty` → "terminate-at-cut-free ⟹ absurd" (fixpoint branches close trivially; obligation
sharpens to `red d = d ⟹ cut-free` + `no cut-free ∅→⊥`); (2) lap-110 cut-formula strip → `hr'`; (3) the ∀/¬
inversion on the engine (template `Zinfty.allInv`). See `REFLECTION-2026-06-25-lap111.md`, `NEXT_STEPS.md`.

**(lap-107 FRESH-MIND REVIEW — historical read.)** Build green **1325**; `src/` UNTOUCHED; headline honest
`sorry` (real `#print axioms = [propext, sorryAx, Classical.choice, Quot.sound]`, 0 math axioms;
`peano_not_proves_consistency` + `not_proves_of_implies_consistency` axiom-clean). Single open obligation =
`goodstein_implies_consistency` = crux-1 (γ→PRWO, DONE axiom-clean lap 57) ∘ **crux-2** (PRWO→Con = the
Gentzen ordinal analysis). **DIRECTION CHANGE this lap (two kernel-verified findings).** The lap-102→106
plan prototyped cut-elimination on external Lean inductives (`ZInf`, `ZcOK`, `ZcDer`). **(1) `ZInf.allInv`
is VACUOUS** — provable by ONE weakening, ignoring `ht` + the `^∀φ` membership (verified by elaborating the
one-liner; `wip/PathCInf.lean`). The META `Zinfty.allInvAux` content is ORDINAL PRESERVATION + ERASURE of
`^∀φ`; `ZInf : V → Prop` has neither, so the port is a weakening. **(2) External inductives are
NON-LOAD-BEARING** — the headline is `IΣ₁ ⊢ Con(PA)`, so the ε₀-descent must hold in EVERY `V ⊧ IΣ₁`,
including non-standard models whose coded ⊥-proof `z` is non-standard, for which no external well-founded
derivation tree exists ⟹ `foundation_bot_to_Z_empty` is unprovable on the prototype. **The load-bearing
carrier is the Σ₁ CODE engine `red`/`iord` (`InternalZ.lean`)**, already arithmetized and total on
non-standard codes (it is what `iord_red_iterate_descends` rides). **THE crux (re-confirmed lap-104):**
engine `red d = znth (redTable d) d` steps via `iRNextG`, which dispatches ONLY on the conclusion's top
`zTag` (4→`iRK`, else→identity); after one K/cut reduction the top is no longer a cut ⟹ `red` stalls ⟹
`iord_descent_red` (`Crux2Blueprint.lean:533`) is unprovable for the current `red`. **NEXT (hardest-first):**
redesign `red`/`iRNextG` to locate + key-reduce the lowest cut anywhere in the ∅→⊥ derivation code (Σ₁
tree-search; the prototype inversion cases are the combinatorial GUIDE), prove `iord_descent_red`, then
`false_of_ZDerivesEmpty` via the `iord`-descent + PRWO → headline. The prototypes (`PathCInf`/`ZcDer`/`ZcOK`)
stay as a sketch — no further investment. crux-2 remains the sole 🟡-active-frontier math content; genuinely
multi-month (faithful internalization of Gentzen's reduction on codes). See `HANDOFF-2026-06-25-lap107.md`,
`NEXT_STEPS.md`, `PENDING_WORK.md` lap-107.

**(lap-101 DEEP REFLECTION — historical read.)** Build green **1325**; headline honest `sorry` (real `#print
axioms = [propext, sorryAx, choice, Quot.sound]`, 0 math axioms; `peano_not_proves_consistency` clean;
faithfulness anchor clean; statement re-audited vs paper, no drift). Single open obligation =
`goodstein_implies_consistency` = crux-1 (γ→PRWO) ∘ **crux-2** (PRWO→Con = `redSound`, internalized
cut-elimination). **Destination + crux-2 target KEPT; the finitary-vs-ω-rule sub-route fork is REOPENED.**
Laps 95–100 pursued Path X (finitary, post lap-95) and made real mechanical progress (the `iRK` gate; the
I∀/I¬/axAll non-Rep replace cases assembled) but did NOT dissolve the wall — it *relocated* from eigensubst
(O2) to the `redZKReady` "hereditary all-Rep selected spine" motive, exactly the conclusion-tracking the
ω-rule retires for free. The motive's hard core is shaky (∅→⊥ chain premises have growing antecedents, so
Cor 2.1 does not reapply down the spine). The lap-92 ω-rule pivot (Path C) was recommended with a de-risk
spike *first*; lap-95 committed to Path X **without running it**. **CALL: run the spike** (`wip/InternalZomega.lean`,
internal ω-rule ∀-node + substitution-free reduct) to settle the fork with evidence; STOP investing in the
`redZKReady` motive / axNeg until then. See `REFLECTION-2026-06-25-lap101.md`, `NEXT_STEPS.md`.

**(lap-95 FRESH-MIND REVIEW — historical read.)** Build green **1325**; headline honest `sorry` (real `#print
axioms = [propext, sorryAx, Classical.choice, Quot.sound]`, 0 math axioms; `peano_not_proves_consistency`
clean). Single open obligation = `goodstein_implies_consistency` = crux-1 (DONE) ∘ **crux-2** = `redSound`.
**The crux-2 wall is now pinned to ONE surgical fix.** O2 (eigenvariable substitution) is DONE
(`ZDerivation_zsubst`, axiom-clean — the lap-78 "substitution wall" was the criticality conjunct, dropped
when `ZPhi` moved to `zKValidF`). O1 (`ZRegular` freshness) was DONE except `ZRegular_red_zK`'s lone
hypothesis `hseltag` (splice ⟹ `zTag dᵢ = 4`), which was FALSE under the old `iRK` (the splice mis-fired
on non-chain selected premises). **This lap LANDED the surgical fix in-kernel:** `iRK`'s splice is now
gated on `zTag dᵢ = 4 ∧ ¬ permIdx dᵢ < lh(zKseq dᵢ)` (critical chain), non-chains routed to the replace
(Buchholz 5.2.2, `red_zK_rep_nonchain`); **`ZRegular_red_zK` is now UNCONDITIONAL and axiom-clean**
(`hseltag` dropped). This is NOT the lap-92 "2–3k-line ω-rule pivot" — the finitary engine + O1 + O2 are
all reused; the ω-rule *selection* reading is just the soundness justification. NEXT: the deep validity
half (`tpReduce` conclusion-reduction for the non-`Rep` replace) + `iord_descent_red` + wire to headline.
See `ANALYSIS-2026-06-25-lap95-dispatch-fix-not-pivot.md`, `PENDING_WORK.md` lap-95 box.

**(lap-92 DEEP REFLECTION — historical read.)** Build green **1325**; headline honest `sorry` (0 math axioms,
faithfulness anchor clean, anti-fraud intact — all re-verified). Single open obligation =
`goodstein_implies_consistency` = crux-1 (DONE) ∘ **crux-2** = `redSound` = internalized cut-elimination.
**The reflection's call: the target is right, the sub-route is not.** crux-2 has been pursued inside
Buchholz's *finitary eigenvariable* system, where cut-elimination needs `d₀(a/n)` substitution that preserves
validity — the O2/lap-78 wall that has held laps 78–91 (route A refuted lap-90, route B `tpReduce` still hits
it, no validity-free bypass). **Recommended pivot (route C): arithmetize the infinitary ω-rule system instead**
(Buchholz §6 `Z^∞`; the repo's `Zinfty.lean` meta engine + Bryce–Goré's Coq both use it). A critical cut then
*selects* the witness premise `dₙ` rather than substituting — dissolving O1+O2+`tpReduce` together. The
ordinal engine (`iord`/`icmp`/`idg`/`iõ`, axiom-clean) is reused unchanged; recursion on `iord<ε₀` is licensed
by PRWO. **NEXT (de-risked): `wip/InternalZomega.lean` spike** to confirm the internal ω-rule reduct is
substitution-free before the ~2–3k-line rebuild. STOP the finitary `tpReduce`/`Zsubst` thread. See
`REFLECTION-2026-06-25-lap92.md`.

**(lap-89 FRESH-MIND REVIEW — historical read.)** Build green **1325**; headline honest `sorry` (real `#print
axioms = [propext, sorryAx, choice, Quot.sound]`, 0 math axioms, anti-fraud intact). M1 + Phase 1 long done;
crux 1 (`γ→PRWO`) landed axiom-clean lap 57. **The endgame is now SINGLE-FRONT:** `PA_delta1Definable` is
discharged UPSTREAM (Foundation proves `𝗣𝗔.Δ₁` as a real instance), so `peano_not_proves_consistency` is
axiom-clean and the ONLY open headline obligation is `goodstein_implies_consistency` (`Reduction.lean:68`) =
crux-1 ∘ **crux-2** = `redSound` = real internalized cut-elimination for the V-internal infinitary system Z.
Laps 84–88 brought all three Buchholz Def-3.2 case-5 dispatch branches to OBJECT-completeness: 5.1 critical
(`iRcritG`/`ZDerivation_iRcritG_of`/`iord_descent_iRcrit_of_chain`), 5.2.2 replace (`iCritAux`/
`ZDerivation_iCritAux_of_zK`/`iord_descent_iCritAux`), 5.2.1 splice (`seqInsert`/`ZDerivation_seqInsert_of_zK`/
`iord_descent_seqInsert'`), plus the dispatch index `permIdx`. **Remaining = ASSEMBLY** (not new descent/
validity math): rewrite `iRNextG`'s tag-4 to DISPATCH on `zKCritical` (→5.1) / else `permIdx` (→5.2.1 if the
selected premise is critical, →5.2.2 if not); then `redSound` (`zDerivation_induction`, tag-4 3-way split) +
unconditional `iord_descent_red` → `iord_red_iterate_descends` → `false_of_ZDerivesEmpty` → `Reduction.lean:68`.

**(lap-74 DEEP REFLECTION — historical read.)** Build green **1323**; headline honest `sorry` (real `#print
axioms = [propext, sorryAx, choice, Quot.sound]`, 0 math axioms, anti-fraud intact; statement re-audited
faithful — no transcription drift). M1 + Phase 1 long done; crux 1 (`γ→PRWO`) landed axiom-clean lap 57.
The single open girder `goodstein_implies_consistency` = crux 1 ∘ **crux 2** (`PRWO→Con`), with crux 2
sharply localized to the lone `InternalZ` obligation **`RedSound`** (the genuine validity-preserving reduct
of a contradiction Z-derivation = real internalized cut-elimination). **Lap 74 re-validated the direction
from altitude and PROVED crux 2 is unavoidable** (the banked free-X monument is the wrong shape; the
specific-instance route still needs Gentzen — no ε₀-strength-free proof exists). Active work = the RedSound
rung ladder (0.5 ✅ → 1 `zsubst` → 2 Ind reduct → 3 K/cut reduct → 4 dispatch), now at `ZDerivation_zsubst`
(rung-1 step 2). Two flagged risks: the lap-70 reduct re-work (`iR2`/`iCritReduct` superseded — stop
extending; `iord`/ω-tower assignment reusable) and the named second front `PA_delta1Definable` (still an
upstream `axiom`, mandatory for axiom-free, untouched). See `REFLECTION-2026-06-24-lap74.md`.

**(lap-71 FRESH-MIND REVIEW — historical read.)** Build green 1321; headline honest `sorry` (real `#print
axioms` = `[propext, sorryAx, choice, Quot.sound]`, 0 math axioms, faithfulness anchor clean, anti-fraud
intact — all re-verified). M1 + Phase 1 (Gödel II hook) long done; crux 1 (`γ→PRWO`) landed axiom-clean
lap 57. The single open math girder `goodstein_implies_consistency` = crux 1 ∘ **crux 2** (`PRWO→Con`),
and crux 2 is now sharply localized to the lone `InternalZ` obligation **`RedSound`**: the `iR2`-reduct of
a contradiction derivation must be a genuine `ZDerivation`. This is real internalized cut-elimination for
the V-internal infinitary system Z (a major multi-lap undertaking; Bryce–Goré's Coq `cut_elim_aux0` alone
is ~420 lines at the *meta* level, the IΣ₁-internalization is harder). **Lap 70 settled the approach**:
Option B (weaken the iterate class so the ordinal-faithful `iR2` preserves it) is REFUTED in-kernel
(`not_zKValid_iCritReduct`); **Option A** (a genuine validity-preserving reduct, shape-dispatched on the
cut formula, à la Bryce–Goré) is forced. Realistic cadence ≈ one genuine reduct rung per lap. Honest
endpoint: best-case headline `[propext, choice, Quot.sound, PA_delta1Definable]`, with `PA_delta1Definable`
the remaining Foundation upstream axiom to discharge for fully-clean.

**(lap-56 FRESH-MIND REVIEW — historical read.)** Build green 1315; headline honest `sorry` (real `#print
axioms` = `[propext, sorryAx, choice, Quot.sound]`, 0 math axioms, faithfulness anchor
`goodsteinSentence_faithful` clean, anti-fraud intact — all re-verified). M1 (`goodsteinTerminates_re`) +
Phase 1 (Gödel II hook) long done. The single open girder `goodstein_implies_consistency` = **crux 1 ∘
crux 2**, decomposed in `wip/GentzenCon.lean` (per-model route, lap 55). **Crux 1** (`γ→PRWO`) is now
isolated to ONE bridge `nonterminating_of_seq_descent`; this review made two corrections to it (see lap-56
summary box): the natCode↔NF order bridge **dissolved** (transparent `icmp` `prwoInstance`, DONE), and the
genuine remaining content is now sharply named — **construct the standard-level domination certificate
(Cor-3.4 slowdown inputs) from the `seq` descent**, which discharges `nonterminating_of_seq_descent` via
`StdCor34.crux1_internal_run_of_width_dom`. **Crux 2** (`PRWO→Con`, Gentzen eq-5 `ord_R_descends`) stays 🟠
generational, parked. Direction VALIDATED: crux 1 is the right hardest-but-tractable target; the lap-55
model-theoretic route is kept, with the bridge specialized (not "arbitrary seq"). Honest endpoint unchanged:
best-case headline `[propext, choice, Quot.sound, PA_delta1Definable]`.

**(lap-53 DEEP REFLECTION — prior read.)** Route A re-derived from the source & KEPT (Goodstein⟹PRWO,
not free-X-TI; §3 is primrec-only). Headline is an honest `sorry` (real `#print axioms` =
`[propext, sorryAx, choice, Quot.sound]`, 0 math axioms, faithfulness anchor clean, anti-fraud intact —
all re-verified this lap, build green 1313). The single open girder `goodstein_implies_consistency` =
**crux 1 ∘ crux 2**, and the two have **asymmetric feasibility**:
- **Crux 1 `γ→PRWO(ε₀)` (Rathjen §3) — 🟡 TRACTABLE, the resolvable doubt, KEEP DRIVING.** ℕ-template +
  internal Thm 3.5 (lap 47) + Lemma 3.6 done; internalizing Cor 3.4 ~80% built (`BlkRec`/`IIter`/`iF`/
  `ipsum`/`InternalGrz`, axiom-clean). Standard-level (lap 50, no internal Ackermann). Remaining = `ig`
  assembly + port g-properties + wire `StdCor34.salpha` + wseq/`icmp`-seams. **A few laps to `γ→PRWO`
  axiom-clean — the campaign's next real milestone.**
- **Crux 2 `PRWO(ε₀)→Con(PA)` (Gentzen Thm 2.8(i)) — 🟠 GENERATIONAL, cited eq-(5), chip opportunistically.**
  Needs `ord`/`R`/eq-(5) `ord(R d)≺ord d` arithmetized **inside PA**. Confirmed NO shortcut this lap:
  Foundation's `Hauptsatz.main` is a meta-level Lean function on the `Derivation` inductive, not a primrec
  PA-function; no arithmetized ordinal analysis exists in Foundation/mathlib; the banked meta-level Thm-5.6
  machine cannot be reused for the internal `ord`. The `wip/GentzenCon.lean` scaffold already isolates it to
  the single cited `ord_R_descends` axiom + proves the meta-descent + all 3 SEAM type-checks.

**Honest endpoint (named this lap):** crux-1 built + crux-2 = cited Gentzen eq-(5) + `PA_delta1Definable`
upstream ⟹ best-case headline `[propext, choice, Quot.sound, PA_delta1Definable]`. This is NOT the strict
trust base; the `PA_delta1Definable` cost is inherent to Route A's Gödel II and needs operator reconciliation
(rec: accept the one disclosed upstream axiom). The banked free-X `peano_not_proves_TI` (0 math axioms) is a
real result but does NOT chain to the headline — keep, don't resurrect, don't delete. See
`REFLECTION-2026-06-23-lap53.md`.

**(lap-47 review — historical read; route is Rathjen Cor 3.7.)** Headline `peano_not_proves_goodstein` is
an honest `sorry` (real `#print axioms` = `[propext, sorryAx, choice, Quot.sound]`, 0 math axioms,
anti-fraud intact). The headline reduces — via the axiom-clean `not_proves_of_implies_consistency` +
Gödel II — to the **one** open implication `Reduction.goodstein_implies_consistency : 𝗣𝗔⊢γ → 𝗣𝗔⊢Con(𝗣𝗔)`
(disclosed `sorry`), faithfully decomposed in its docstring into TWO deep girders:
1. **§3: `𝗣𝗔⊢γ → 𝗣𝗔⊢PRWO(ε₀)`** (all primrec). Pipeline: internal **Cor 3.4** (raw primrec ε₀-descent →
   *slow* α with `iC(αₙ)≤K(n+1)`; Grzegorczyk `g`-padding, **internal level `l:V` ⟹ Ackermann, not
   IΣ₁-total ⟹ needs the PA substrate, not the IΣ₁ `PR.Construction` toolkit**) → internal **Thm 3.5**
   (slow α → `β` with tight `iC(βᵣ)≤r+1`, **COMPLETE lap 47** — `bbeta_isNF`/`bbeta_C_le`/`bbeta_desc_exists`,
   the ω-tower cofinality boundary now discharged) → **Lemma 3.6** (`DescentArith.nonterminating_internal`,
   done) ⟹ a non-terminating special Goodstein run, contradicting γ.
2. **`PRWO(ε₀) → Con(𝗣𝗔)`** (Gentzen Thm 2.8(i), PRA-provable): primrec ordinal assignment `ord` + reduction
   `R` with `ord(R D)<ord D`, arithmetized over Foundation's `Derivation`. THE deep ordinal-analysis girder.
   Prereq: formulate `PRWO(ε₀)` as a `Sentence ℒₒᵣ`.

**Two open deep cruxes (hardest-first), both multi-lap:** (a) **internal Cor 3.4** (the harder — internal
Grzegorczyk level over `V ⊧ 𝗣𝗔`; recommended first attack = parameterize over an abstract internal `f`
with its recursion eqns + Lemma-3.2 domination as hypotheses, per PENDING_WORK lap-45 path #2), and (b)
**Gentzen Thm 2.8** + the `PRWO` sentence. Plus the residual 🟡 `PA_delta1Definable` (Foundation axiom under
Gödel II — see ledger). The ℕ-template substrate (`Grzegorczyk.lean` Lemma 3.3 + Cor 3.4 bricks, sorry-free)
is the blueprint for (a). Internal Thm 3.5 (lap 47) is route-independent and survives any route change.

**(lap-44 reflection — historical read; predates the route resolution.)** The ordinal-analysis girder is **done and axiom-clean** (real
`#print axioms peano_not_proves_TI` = trust-base + 1 🟢 native_decide); the headline
`peano_not_proves_goodstein` is an honest `sorry` (0 math axioms, anti-fraud intact);
`goodsteinSentence_faithful` is clean. The ENTIRE project reduces to **one obligation** inside
`no_min_descent_absurd_of_goodstein` (`DescentSemantic.lean`). **Crisp re-statement of that obligation:**
the consumer side is DONE — `nonterminating_of_xDescent` (X-essential, `lx_succ_induction`),
`slowdown_run_facts` + `ineq6_step_internal` (internal Lemma 3.6), and `DescentCore` Thm 3.5 reindex
(`C_betaTail_le`/`repr_betaTail_*`, ℕ) + Lemma 3.6 (`lemma36_nonterminating`, ℕ) all built. **What
remains is exactly: produce the M-internal X-definable slowed code sequence `β : M → M`** with
`isNF`/`iCanon (k+1)` (`C(βₖ) ≤ k+1`)/`icmp`-descent + LX-definable run-comparison (`hPdef`), from the
X-definable descent (`descentR`/`descent_iterate_seq_total`, done). I.e. Rathjen §3 Cor 3.4 + Thm 3.5
internalized on codes. **⚠ lap-44 finding (A):** the literal `sorry` at `DescentSemantic.lean:574` still
routes through the **DEAD 𝚺₁ path** (`hbound`+`nonterminating_internal`), whose `𝚺₁-Function₁ b` shape is
**unachievable** (b is X-dependent) — rewire to `nonterminating_of_xDescent` first (next action). **⚠ (B):**
`Grzegorczyk.lean` collapses Rathjen's length-`|·|` 3.3/3.4 onto **C** — finish the ℕ Cor 3.4 assembly to
verify the C-collapse before M-internalizing. See `REFLECTION-2026-06-23-lap44.md`.

**(lap-39 review — historical read.)** The ordinal-analysis girder is **done and axiom-clean** (real `#print
axioms peano_not_proves_TI` = trust-base + 1 🟢 native_decide); the headline `peano_not_proves_goodstein` is
an honest `sorry` (0 math axioms, anti-fraud intact); the faithfulness anchor `goodsteinSentence_faithful` is
axiom-clean. The ENTIRE project now reduces to **one obligation**: `hbound` (`DescentSemantic.lean:416`),
inside `no_min_descent_absurd_of_goodstein`. Laps 37–38 built the **internal ε₀-notation arithmetic**
(`InternalONote.lean`, sorry-free, axiom-clean): codes + `iC` + `ievalNat` (T̂) + `iCanon` + `icmp` + `isNF` +
**order-reflection** `ievalNat_lt_of_icmp_eq_zero` (Rathjen 2.3(iii)). This is the deep substrate `hbound`'s
`step` consumes. **Decomposition of `hbound` (the live attack, hardest-first):** (1) internal
`evalNat_succ_base` `ievalNat (b+1) c = ibump (b+1) (ievalNat b c)` (structural induction; needs the tail
bound — already in `evalNat_reflect_combined`'s TB — + 3 digit-peel lemmas `ilog`/`div`/`mod` of a leading
term, `ibump_pos` recursion in hand); (2) internal `ineq6_step` (port `DescentCore.ineq6_step` digit-direct
onto codes, consuming order-reflection + (1)); (3) seam/F re-wire to transparent `natCodeT` (route (b), the
risky girder touch — re-`#print axioms peano_not_proves_TI` after every change); (4) βₖ slow-down (Rathjen
Thm 3.5) + assemble `hbound` (`base`/`step`/`hpos`+`𝚺₁`-def). Fully offline. See `HANDOFF-2026-06-23-lap38.md`.

**(lap-36 reflection + wall B dissolved — historical read.)** The ordinal-analysis girder is **done and
axiom-clean**; the headline is **one theorem** away (`DescentSemantic.no_min_descent_absurd_of_goodstein`).
Lap 36 found wall B was self-inflicted by the opaque `codeOfREPred` blob, **refactored `goodsteinSentence`
transparent** (`“∀ m ∃ N, !igoodsteinDef 0 m N”`, faithful bridge re-proved clean), and **discharged `hB`**.
The project's only literature gate is gone (`ON-LINE-REQUEST` archived). **The lone genuine remaining wall
is `hCD`** (wall C+D): Rathjen §3 slow-down internalized in `M` — extract a coherent descent function from
`descent_seq_exists` (lap 35), construct `βₖ` + internalize the `DescentCore` ONote/`C` kernel into `M`'s
reduct as `LX`-definable functions, wire the run side (`DescentArith.nonterminating_internal`). Fully
offline. See `REFLECTION-2026-06-23-lap36.md`.

**(lap-33 review — historical read.)** ONE wall stands between the disclosed-`sorry` headline and a fully
axiom-clean Kirby–Paris: **`DescentSemantic.no_min_descent_absurd_of_goodstein`** (Rathjen §3 *inside a
model `M ⊧ paLX`*). Real `#print axioms` this lap: `Thm56.peano_not_proves_TI` (the whole Buchholz Thm 5.6
girder) = `[propext, choice, Quot.sound, ONoteComp…native_decide]` — **clean**; the would-be-headline chain
`peano_not_proves_goodstein_modulo_semantic` adds **exactly one `sorryAx`**, from that lemma. Laps 31–32
built the **equality plumbing** the lemma's substrate needs: X-congruence (`relExt Xsym`) is now an axiom of
`paLX` (lap 32 `a0c611f`, `peano_not_proves_TI` re-validated clean), and `𝗘𝗤 ⪯ paLX` is proved (lap 32
`32d0b0e`) — so models of `paLX` carry genuine equality. **Immediate gate (A2 part 2):** re-route `descentE`
through `Structure.consequence_iff_eq` + `complete` so `no_min_descent_absurd_of_goodstein` may assume
`[Structure.Eq LX M]` — required to install `M`'s `ℒₒᵣ`-reduct as a real `[M ⊧ₘ* 𝗜𝚺₁]` (the substrate
lemmas `ReductModel.reduct_models_isigma1` already demand it). **Then the deep content (walls B/C/D):**
B (opaque `codeOfREPred goodsteinTerminates` ↔ `∃N, igoodstein m N=0`, IΣ₁-internal), C (M-internal
`Mlt`-descent via LX least-number), D (slow-down `βₖ` + `DescentCore.ineq6_step` iterated by `M ⊧
InductionScheme LX`). Substrate is built (laps 26–32); this is the genuine remaining mathematics.

**(lap-30 read.)** The project has **one wall left, and it is now a single semantic lemma**:
`DescentSemantic.paLX_models_TI_of_PA_provable` — "if `𝗣𝗔 ⊢ goodsteinSentence`, every model `M ⊧ paLX`
satisfies `TI prec`." Everything else is machine-checked: `peano_not_proves_TI` (Thm 5.6) is axiom-clean
(lap 28, F-φ discharged), and `DescentSemantic.descentE : Thm56.DescentE` derives the whole `Derivation2
paLX {TI prec}` from that one lemma via Foundation's completeness theorem. `#print axioms` on the full
chain (`peano_not_proves_goodstein_modulo_semantic`) = trust-base + 1 🟢 `native_decide` + 1 `sorryAx`;
discharging the semantic lemma makes the headline clean. **Attack (`DESCENT-PLAN §5`):** decompose
`paLX_models_TI_of_PA_provable` model-internally — (1) E-lift+soundness ⟹ `M ⊧ lMap goodsteinSentence`
(easy, next); (2) the `¬TI prec` ⟹ X-definable `≺`-descent in `M` via `M`'s LX least-number principle;
(3) Rathjen §3 slow-down + inequality (6) in `M` (the lap-26 substrate run + `DescentCore.ineq6_step`,
iterated by `M ⊧ InductionScheme LX`); (4) contradiction with (1). The lap-26 internal substrate transfers
directly; the `sigma1_pos_succ_induction`/`DescentInternal` lemmas are true and green but now superseded
(they were the `V ⊧ 𝗜𝚺₁`, X-free framing — the model `M ⊧ paLX` framing here is the one that closes).

**(historical lap-27 read.)** The project has effectively **one wall left: E-core (Route-B form)**. F-φ —
the lone math axiom under `peano_not_proves_TI` — was **SOLVED on Aristotle** (`rePred_ltPull_natCode`,
verified-faithful, `wip/aristotle-fphi/`); only a mechanical `v4.28→v4.31` port stands between it and
discharge. The **back-end is decided: Route B** (the built, axiom-clean Buchholz monument), reversing the
"deferred" framing — the lap 25–26 internal-V `sigma1_pos_succ_induction` route lands X-free
`𝗣𝗔 ⊢ PRWO`, which is **Route A's** antecedent and cannot feed `peano_not_proves_TI` (free-`X`
obstruction). E-core(b) must be re-targeted to the **integrated paLX construction** (X-definable descent
+ `InductionScheme LX`), reusing the lap-26 arithmetic substrate. Real `#print axioms` (lap 27, build
1280 jobs): headline `[propext, sorryAx, choice, Quot.sound]` (honest `sorry`, 0 math axioms);
`peano_not_proves_TI` = `[propext, choice, Quot.sound, rePred_ltPull_natCode]` (exactly 1 math axiom,
F-φ, now proof-in-hand).

**(historical lap-24 read.)** `peano_not_proves_TI` (Buchholz Thm 5.6, `𝗣𝗔 ⊬ TI_≺(X)`) is **assembled and
axiom-clean modulo the single F-φ axiom** `rePred_ltPull_natCode` (on Aristotle): the full §5 chain
C₂→C₁→D→F + D' (`embed_TI_bounded`, discharged lap 22 via `EmbeddingBound.embedC_LX_bdd`). The headline
reduces to it through `peano_not_proves_goodstein_of_descent` modulo **E** = `DescentE`
(`𝗣𝗔 ⊢ goodsteinSentence → Nonempty (Derivation2 paLX {TI prec})`). E factors as **E-lift** (proof
translation, X-free, DONE lap 23: `paLX_derivable2_lMap_of_PA_provable`) **∘ E-core** (Rathjen §3
"slowing-down" inside PA: `𝗣𝗔 ⊢ goodstein → 𝗣𝗔 ⊢ PRWO(ε₀)`, plus the `PRWO ⟹ TI prec` X-induction
instance). E-core is the **last deep wall**; lap 23 landed its first semantic brick (`evalNat`
order-reflection, `src/DescentCore.lean`). Below the headline only **2 honest `sorry`s** remain in
`src/`: the locked headline (`Statement.lean:22`) and off-path Route-A (`Reduction.lean:52`).

**Historical (the machine from D back, machine-checked + `#print axioms`-clean, lap 18):** the
**embedding** M4 `embedC` (Thm 5.5, `src/Embedding.lean`), the **ε₀ cut-elimination** M5
`cutElim` (Thms 5.1–5.3, `src/Zinfty.lean` + generic `src/ZinftyGen.lean`), **lap 14's Boundedness** Thm
5.4 + corollary `Z∞⊢^β_1 TI ⟹ ‖≺‖≤2^β` (`src/Boundedness.lean`), **lap 15/17's C₁** `PXFc.cutElim`→cr0 +
**D** `orderType_le_of_TIprovable` (`src/XFreeCutElim.lean`, made axiom-clean lap 17 via `nrel_value_subst`),
and **lap 16/17's C₂-structural** `embedC_LX_gen` (`src/EmbeddingX.lean`). Phase 0 (M1,
`goodsteinTerminates_re` clean) + Phase 1 (Gödel II hook) landed. The **only `sorry` below the headline**
(besides the locked headline + off-path Route-A `Reduction.lean:50`) is **C₂ glue** `hax_paLX`'s
X-induction assembly (`EmbeddingX.lean:705`, base done, recipe inlined). The headline
`Statement.peano_not_proves_goodstein` is **still a literal `sorry`** (anti-fraud — correct; `#print axioms`
= `[propext, sorryAx, choice, Quot.sound]`, 0 math axioms). Closing `hax_paLX` makes **Thm 5.6 =
`PA ⊬ TI(ε₀)`** axiom-clean modulo the two remaining campaign girders: the bridge (E, Goodstein⟹TI) +
arithmetization seam (F, `‖≺‖=ε₀`; order-type half = ε₀-completeness, mathlib-lacking — see lap-18 focus).
**Lap-12 pivot** (see route decision):
the project drifted (laps 4–11) into Towsner's witness-bounded variant and hit a genuine wall (§19.6
witness-budget needs the operator `H`). Buchholz §5 shows the witness-FREE route — M4+M5 (done) +
**Boundedness (Thm 5.4)** + Goodstein⟹TI(ε₀) — is the standard, shorter path. Next target = the truth
semantics `⊨^α` + Boundedness. M6 (Hardy lower bound) and the `wip/` witness-bounded calculi are banked
off-path. See `ANALYSIS-2026-06-22-lap12-buchholz-pivot.md` and Outstanding.

## Route decision (lap 12) — PIVOT to Buchholz's Boundedness route (RETRACTS the lap-7 Route-B choice)
**Decision: the Gentzen/Buchholz `TI(ε₀)` route, via Boundedness (Thm 5.4) on the witness-FREE `Z∞`.**
The lap-7 "stay on Towsner Route B" rested on a claim that **lap 12 falsified**: the `(α,k)` cut-elim was
NOT a resolved bookkeeping detail — its §19.6 commuting-ω case is provably unclosable with any numeric
control (ADDENDUM 7), needing the Buchholz operator `H` (multi-lap). Meanwhile Buchholz §5 shows the
witness-FREE route reuses **M5 cut-elim (done) + M4 `embedC` (done)** and needs only **Boundedness +
Goodstein⟹TI(ε₀)** — strictly less unproven surface than Towsner's `Zᵏ` + bounded-cut-elim + bridge, and
the textbook-standard analysis. M6 (Hardy lower bound) was the main "Route B asset" justifying the lap-7
choice, but it is Towsner-specific and now OFF the critical path (banked, not deleted). See
`ANALYSIS-2026-06-22-lap12-buchholz-pivot.md`. (Route A via `Con(PA)`+Gödel-II stays the documented
escape hatch; it re-introduces the `PA_delta1Definable` Foundation axiom 🟡.)

## What's happened (newest first)
- **2026-06-27 (lap 161 — DEEP REFLECTION, every-9th):** Re-verified in-kernel (real `#print axioms`, green 1326,
  exit 0): headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms, bare sorry), `peano_not_proves_consistency`
  + `goodsteinSentence_faithful` clean, `false_of_ZDerivesEmpty` 0 math axioms — no drift. **RE-SYNCED the stale lap-158
  directive.** FINDING: lap-158 was internally contradictory — its review half mandated an "outer degree-induction design
  spike FIRST," but its OWN spike (`9ac1bf3`) REFUTED that hypothesis (the {3,4} producer closes by the EXISTING
  code-induction with LOCAL per-flatten degree headroom, `irk+1 ≤ idg(premise)`, NO global degree-induction). Laps 159-160
  then WIRED + CLOSED that {3,4}-producer core in-kernel (`repProducerClose` via `certReplace_of_premise_cert` + general IH;
  consumed in the live dispatch `Crux2Blueprint:3578-3581`). So "the irreducible heart of crux-2" (Buchholz Thm 2.1) is
  CRACKED; the open `residual` (:3451)/`axMajorResidual` (:3735) now hold ONLY the STRUCTURAL escape set — (i) ⊥-exit
  ex-falso (needs internal ⊥-elim/weakening, the one new piece), (ii) C-exit R-intro replay, (iii) tag-5/6 thread-escape
  (shared). VERDICT = progress GENUINE (residual content shrank monotonically 148→160) but laps 155-160 added 3 anySucc
  leaves WITHOUT a whole-lemma DROP — next laps must DROP. MANDATE (DIRECTION.md lap-161) = build the internal
  ex-falso/weakening lemma FIRST, wire it + R-intro replay + shared thread to CLOSE `residual` → collapses FOUR of six
  sorries; gDef (:4309) separable. FORBIDDEN = re-spiking the {3,4} producer / outer degree-induction (DONE + refuted);
  `red`; `iord`-recursion; `redLeast`; refuted `seqUpdate` splice; axMajor/gDef standalone before the port; M2/M3/M4.
  ALTITUDE CAUTION (sharpened) = `false_of_ZDerivesEmpty` sorry-free is NOT the headline (`goodstein_implies_consistency`
  `Reduction.lean:68` bare sorry, NOT YET wired; M2/M4 bridge ~0% built). See `REFLECTION-2026-06-27-lap161.md`,
  `DIRECTION.md` lap-161.
- **2026-06-27 (lap 158 — FRESH-MIND REVIEW):** Re-verified in-kernel (real `#print axioms`, green 1326):
  headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms), `peano_not_proves_consistency` +
  `goodsteinSentence_faithful` clean, `false_of_ZDerivesEmpty` 0 math axioms — no drift. **Direction KEPT;
  lap-155's SUCCEDENT-THREADING COLLAPSE mandate DONE + EXHAUSTED** (laps 155-157 closed every threadable
  sub-case of `axMajorResidual` `:3417`: tag-5(a), tag-6(a), zAxNeg producer, and — lap 157,
  `climb_to_rep_producer` axiom-clean — the tag-5 zAxAll producer). VERDICT = progress GENUINE (steady crux
  narrowing 153→157, not fixation/leaf-neglect). **FINDING:** the residual is now the IRREDUCIBLE
  {3,4}-producer cut-reduction = Buchholz Thm 2.1 general cut-elimination (the heart of crux-2), NOW
  UN-FORBIDDEN (the collapse-to-exhaustion gate is met): a NON-LEAF `Rep` node that PRODUCES the cut formula,
  un-threadable AND un-reducible by same-degree õ-drop (REFUTED in-kernel lap 157). Shapes: (i) tag-5+climb →
  `^∀^k⊥` (∀-tower over closed ⊥, dominant); (ii) tag-6 → arbitrary `p'`. MANDATE = DESIGN SPIKE first (wip/,
  lap-101/132-style) pinning the DEGREE-induction generalized statement (outer on the NAT `idg`, inner on
  code, eliminate highest-rank cuts first, generalize `genReduct_botSucc` off `seqSucc=⊥` reusing the
  same-end-sequent `certReplace`; explore the cheap `^∀⊥→⊥` inversion for (i)), THEN port to src as named
  sub-`sorry`s. FORBIDDEN = blind src refactor before the spike; same-degree õ-drop (refuted lap 157); `red`;
  `iord`-recursion; `redLeast`; axMajor/gDef standalone. See `DIRECTION.md` lap-158, `PENDING_WORK.md` lap-158.
- **2026-06-27 (lap 155 — FRESH-MIND REVIEW):** Re-verified in-kernel (green 1326): headline `[propext,
  sorryAx, choice, Quot.sound]` (0 math axioms), faithful/consistency/`false_of_ZDerivesEmpty` re-audited —
  no drift. **Direction KEPT; lap-152's mandate DONE** (MASTER KEY #1 hasRedex DROPPED lap 153, #2 noRedex
  6/8 PROVEN lap 154); termination crux isolated to the SINGLE leaf `axMajorClose` (tag-5/6, `:3418`).
  **COURSE-CORRECTION** off the lap-154 handoff's "(b) = lap-136 general-succedent reduct": kernel-grounded
  that the cut formula is `^∀⊥` (`p=⊥`) and `hnolow` forbids *creating* `^∀⊥` below j0 (a direct R-intro
  `zIall` would `isRedexPair` with jstar — VERIFIED `isRedexPair:4820` fires on `(zIall ^∀p, zAxAll ^∀p)`),
  so `^∀⊥` only threads from Γ. MANDATE = the SUCCEDENT-THREADING COLLAPSE (sub-case (a) `^∀⊥∈Γ` via 2
  reusable ordinal lemmas + cut-partner generalization; collapse (b) via leaf-threading/`hnolow`/zK-recurse),
  NOT lap-136 (tested first, most likely obviated). See `DIRECTION.md` lap-155, `PENDING_WORK.md` lap-155.
- **2026-06-27 (lap 152 — DEEP REFLECTION, prev lap-143):** Re-verified in-kernel (green 1326): headline
  `[propext, sorryAx, choice, Quot.sound]` (0 math axioms), `goodsteinSentence_faithful` +
  `peano_not_proves_consistency` clean, statement re-audited — no drift. **Direction KEPT** (existence-form
  pivot off `red` + lap-150 code-recursion frame). **Trajectory judged HEALTHY:** the lap-143 worries
  (banking-not-wiring, witnessing with `red`) are RESOLVED; laps 144→151 are genuine steady crux DROPS
  (live path off `red` 144; `descent_step_Ind` 146; §5.2 has-redex 147; tag-3 freshFlag 149; code-recursion
  frame `genReduct_botSucc` 150; in-kernel refutation of the `seqUpdate` splice + FLATTEN engine
  `descent_step_K_spliceHalves` + false `descent_step_K_splice` DELETED 151) — no fixation, no dead-end
  circling. **KEY ARCHITECTURAL INSIGHT:** the four open live leaves reduce to **TWO master keys**
  (`genReduct_chain_hasRedex` :2989 + `genReduct_chain_noRedex` :3013) which SUBSUME the outer
  `descent_step_K_noncrit_axMajor` :3226 (the `Γ=∅` cut-partner special case) and FEED `gDef` :3349 (needs the
  constructive cert reduct) — do NOT attack `axMajor`/`gDef` standalone. **MANDATE (DIRECTION.md lap-152):**
  DROP `genReduct_chain_hasRedex` via the zSeqAnt tag-4 `Seq (seqAnt s)` fold (`zSeqAntNext` `Zsubst:2003` →
  always `seqAntSeqFlag (fstIdx d)`; the proven lap-149/146 fold shape), THEN `genReduct_chain_noRedex`.
  **ALTITUDE CAUTION elevated:** M2 (Foundation→Z bridge) ~0% built + crux-entangled — "only the crux is left"
  ≠ "almost done." Docs: `REFLECTION-2026-06-27-lap152.md`, `DIRECTION.md` CURRENT DIRECTIVE (lap-152).
- **2026-06-26 (lap 149 — FRESH-MIND REVIEW):** Re-verified in-kernel (green 1326): headline + crux-2 chain
  (`false_of_ZDerivesEmpty`/`ZDerivesEmptyR_descent_step`/`descent_step_K_noncrit_recurse`) all
  `[propext, sorryAx, Classical.choice, Quot.sound]` (0 math axioms), statement re-audited — no drift.
  **Course-correction:** lap-146's mandate is DONE (`descent_step_Ind` DROPPED lap 146; laps 147-148 advanced
  Buchholz §5.2 noncritical — has-redex half PROVEN lap 147, no-redex decomposed per §14.254a/b lap 148, tag-3
  repMajor proven modulo the freshFlag residual). Crux-2 is now **4 disclosed `sorryAx` leaves**
  {tag-3 freshFlag :2974, tag-4 K-recursion :2934, axMajor 5/6 :3002, gDef :3125}. **Finding:** a crux-neglect
  signal is forming — recent laps closed the surrounding machinery while the genuine crux (general `Γ→⊥`
  cut-reduction by code-induction, leaves 2934+3002) stays untouched; tag-3 freshFlag is the LAST tractable
  leaf. **MANDATE (DIRECTION.md lap-149):** DROP tag-3 freshFlag via the focused `zFreshNext` tag-3→`freshFlag`
  strengthening (mirror tag-1 I∀ `Zsubst:1671`, exact shape of the proven lap-146 `zIndWff` ripple), THEN turn
  to the crux (general code-recursion + gDef) — NO more leaf-hunting. FORBIDDEN = `red` witnesses;
  `iord`-recursion for the general step; `redLeast` for gDef. Docs: `DIRECTION.md` CURRENT DIRECTIVE (lap-149),
  `HANDOFF-2026-06-26-lap149.md`, `PENDING_WORK.md` lap-149.
- **2026-06-26 (lap 143 — DEEP REFLECTION):** Re-verified in-kernel (green 1326): headline
  `[propext, sorryAx, Classical.choice, Quot.sound]` (0 math axioms), `goodsteinSentence_faithful` +
  `peano_not_proves_consistency` clean, statement re-audited — no drift. **Altitude finding:** the lap-132
  existence-form pivot was right and stays, but laps 141-142 half-abandoned its discipline — `descent_step_K_critical`
  (:1891) re-witnesses the bare-`∃` step with `red` (`ZDerivesEmptyR_red` → the FALSE/incomplete `redSoundGen` :1471,
  which invokes kernel-FALSE `zKValidF_iIndReduct_of_zInd` :80 + open zK :1508 + kernel-FALSE `ZDerivation_red_zK_crit`
  :1108), so the live path still leans on two kernel-verified-FALSE sorries; the genuine red-free `ZDerivation_iRKcCrit_critical_all`
  (:1847, lap-142) is banked but UNWIRED (zero false-dependence dropped). Trajectory 128→142 = 14 laps of
  decompose/bank/re-decompose with the load-bearing sorries never dropping. MANDATE (DIRECTION.md lap-143): derive
  `ZSeqAnt_iRKcCrit`, split `descent_step_K_critical` ∀ (wire `iRKcCrit`)/¬ (named `redexJ≤j0`), re-witness Ind with
  `iIndReductSeqG`; FORBIDDEN = witnessing any descent branch with `red`. Docs: `REFLECTION-2026-06-26-lap143.md`,
  `DIRECTION.md` CURRENT DIRECTIVE (lap-143), `PENDING_WORK.md` lap-143.
- **2026-06-26 (lap 140 — ALTITUDE REVIEW):** Re-verified in-kernel (green 1326): headline
  `[propext, sorryAx, Classical.choice, Quot.sound]` (0 math axioms), `goodsteinSentence_faithful` clean — no
  drift. **Course-correction:** the lap-137 CURRENT DIRECTIVE was materially stale (it still mandated the
  `redLeast` μ-min route for (A) — REFUTED lap 139 — and pointed at the orbit (B) — PROVEN lap 138). Corrected
  `DIRECTION.md`: the entire crux-2 termination now collapses to ONE lemma `descent_step_K_majorIdx`
  (`Crux2Blueprint:1764`) — M3 `false_of_ZDerivesEmpty` is sorry-free given `InternalPRWO V` + the bare-∃ step,
  orbit (B) proven, and (A) folds in via the concrete `redStep`. MANDATE = decompose it into per-tag {3,4,5/6}
  named src sub-`sorry`s + assemble a banked sub-piece to a DROP. Laps 135→139 are a converging campaign (not
  fixation): 135 spike, 136 `iIndReductSeqG`, 137 type-fix+decompose, 138 orbit closed, 139 pair-parametric
  tag-5/6 half-layer. Yellow flag noted: lap-139 dropped no src sorry; the fix is to assemble, not bank.
  Docs: `DIRECTION.md` CURRENT DIRECTIVE (lap-140), `HANDOFF-2026-06-26-lap139.md`, `PENDING_WORK.md`.
- **2026-06-26 (lap 132 — DEEP REFLECTION):** Re-verified in-kernel (green 1326): headline + girder
  `[propext, sorryAx, choice, Quot.sound]` (0 math axioms), `goodsteinSentence_faithful` +
  `peano_not_proves_consistency` axiom-clean; statement re-audited vs source (`bump`/`goodsteinSeq` genuine
  hereditary bump) — no drift. **Altitude call:** crux-2's diagnosis is converged and correct, but the
  SELECTION/STALL sub-goal consuming laps 120→131 is an artifact of the *fixed-deterministic-engine*
  formulation. Recommended a course-TEST: reframe `false_of_ZDerivesEmpty`'s iteration to `redLeast` (Σ₁ least
  descending reduct), making "fixpoint ⟹ cut-free" definitional via one existence lemma (E) — obviates the
  permIdx-selection campaign (`firstBotPrem`/`majorIdx`/tag-dispatch/ZPhi exact-shape) while reusing the banked
  soundness (112-119), invariant folds, and per-reduct descent. (E) discharges at the ⊥-root from banked facts
  (`zTag_Ind_or_K_of_ZDerivesEmpty` + `iord_descent_iRKcCrit_corr`/`_zInd` + Cor 2.1). NEXT = `wip/` spike.
  Docs: `REFLECTION-2026-06-26-lap132.md`, `NEXT_STEPS.md`, `PENDING_WORK.md` lap-132.
- **2026-06-26 (lap 120 — DEEP REFLECTION):** Re-verified kernel in-kernel (`lake env lean`, green 1326):
  headline + girder `[propext, sorryAx, choice, Quot.sound]` (0 math axioms), `peano_not_proves_consistency`
  clean; statement re-audited vs paper — no drift. **Surfaced the genuine open crux the grind couldn't see:**
  the endgame `false_of_ZDerivesEmpty` (bare sorry) cannot close because `red` STALLS — `permIdx` can select
  an atom/`zAx1` premise (`iperm isymRep` unconditional), making a tag-4 K-node a `red`-fixpoint that is not
  cut-free (the repo flags this in `RedZKDescent.lean`). Lap-111's disjunctive `iord_descent_red` RELOCATED
  the stall into the unbuilt `false_of_ZDerivesEmpty` rather than fixing it; same defect as laps 104/107,
  still open. The inversion work (112–119) solved a different sub-problem (reduct SOUNDNESS ≠ termination).
  **Course correction:** highest-value next target = **(A)** `red w = w ∧ ZDerivesEmptyR w ⟹ False`
  (fixpoint-absurdity; vacuity-of-stall first, probe `ZRegular`), not the atomic engine swap. See
  `REFLECTION-2026-06-26-lap120.md`. SECOND FINDING (kernel-grounded, continuation): `zKValidF_iIndReduct_of_zInd`
  (`Crux2Blueprint:79`) is FALSE as stated — the `k=1` Ind reduct `⟨d1,d0⟩` has `chainAsucc ∈ {F(a+1),F(0)}`,
  unable to satisfy the `isChainInf` exit `= F(t)` for `t≠0`; same instance defect as lap-114's critical reduct
  (ordinal-invariant, validity-broken). Fix = instance-correct Ind reduct; AUDIT splice/replace for the same.
- **2026-06-26 (lap 117 — FRESH-MIND REVIEW + ¬-case inversion):** Validated the lap-116 "engine re-key"
  direction but found its hidden prerequisite: a CLEAN re-key needs the I¬ critical sub-case (else the
  sorry-free descent/regularity lemmas regress). Proved it: the ¬-case critical-cut inversion SOUNDNESS
  (`iRcritGNeg` + `ZDerivation_iRcritGNeg_of` + `_haux0_neg`/`_haux1_neg` + `ZDerivation_iRcritGNeg_corrected_neg`),
  all axiom-clean. Key structural finding: the ¬-case SWAPS the two halves' redex assignment (Buchholz 5.1
  ¬-subcase), so `iRcritG` cannot express it. One §5 residual: `zAxNeg` needs the `A∈Γ` side condition. Build
  green 1326; headline footprint + 8 Crux2 sorries unchanged.
- **2026-06-25 (lap 111 — DEEP REFLECTION):** Re-verified kernel in-kernel (`lake env lean`, green 1326):
  headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms), `goodstein_implies_consistency` same lone
  `sorryAx`, `peano_not_proves_consistency` + `not_proves_of_implies_consistency` + `goodsteinSentence_faithful`
  all clean; statement re-audited vs paper (Π₂ `∀m∃N goodsteinSeq m N=0`) — no drift. **Direction KEPT.**
  Found: lap 110 was real progress (the `iCritReductG` principal-vs-stripped cut-formula root cause), but the
  effort is IMBALANCED — the ordinal-DESCENT bookkeeping (`iord_descent_red`, ~80%) has absorbed the laps while
  the ∀/¬-INVERSION (`ZDerivation_red_zK_crit`, the genuine cut-elimination content, ≈0% on the engine; its only
  attempt `ZInf.allInv` killed VACUOUS lap 107) sits untouched. The `iord_descent_red` fixpoint branches are a
  SELECTION bug re-surfacing across laps 104/107/109/110, not descent gaps. **CALL:** (1) reformulate
  `iord_descent_red` → disjunctive `red d = d ∨ iord ≺` + `false_of_ZDerivesEmpty` → terminate-at-cut-free-absurd
  (fixpoint branches close trivially; obligation sharpens to selection-correctness + no-cut-free-⊥); (2) lap-110
  cut-formula strip → `hr'`; (3) the inversion (prize). Fixed `Reduction.lean` doc-drift (no longer claims
  `peano_not_proves_consistency` carries `PA_delta1Definable` — clean since lap 89). Wrote
  `REFLECTION-2026-06-25-lap111.md`; refreshed STATUS + NEXT_STEPS + HANDOFF.
- **2026-06-25 (lap 101 — DEEP REFLECTION):** Re-verified kernel in-kernel (`lake env lean`, green 1325):
  headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms), `peano_not_proves_consistency` clean,
  faithfulness anchor clean, statement re-audited vs paper (genuine hereditary base bump) — no drift.
  **Destination + crux-2 target KEPT; sub-route fork REOPENED.** Found the lap-95 Path-X commitment was made
  on the de-risk spike lap-92 explicitly said to run *first* — which was never written (`find` confirms no
  `InternalZomega` ever existed). Laps 95–100 (Path X) made real mechanical progress but the wall *relocated*
  (eigensubst → the `redZKReady` hereditary-all-Rep motive) rather than dissolving; the motive's hard core is
  shaky (∅→⊥ chain premises have growing antecedents ⟹ Cor 2.1 doesn't reapply down the spine). **CALL: run
  the skipped spike** to settle finitary-vs-ω-rule with evidence; STOP investing in the motive/axNeg until the
  verdict. Wrote `REFLECTION-2026-06-25-lap101.md` + `NEXT_STEPS.md`; refreshed STATUS + PENDING_WORK. NEXT =
  `wip/InternalZomega.lean` (internal ω-rule ∀-node + substitution-free critical-cut reduct).
- **2026-06-25 (lap 95 — FRESH-MIND REVIEW):** Re-verified kernel (real `#print axioms`, green 1325): headline
  `[propext, sorryAx, choice, Quot.sound]` (0 math axioms), `peano_not_proves_consistency` clean. **Direction
  KEPT, Path X CONFIRMED + SHARPENED.** Dissolved the lap-92 "Path X vs ω-rule pivot / 2–3k-line rewrite"
  fork by reading the kernel: **O2 DONE** (`ZDerivation_zsubst` axiom-clean) and **O1 DONE except one leaf**
  (`ZRegular_red_zK` proved modulo the lone hypothesis `hseltag`). The entire remaining regularity wall = that
  ONE false hypothesis (`hseltag`: splice ⟹ `zTag dᵢ = 4`, FALSE under the old `iRK` splice dispatch).
  Fix = a SURGICAL gate (splice only when dᵢ is a critical chain); the ω-rule *selection* reading is just the
  soundness justification, not a rebuild. **LANDED the gate IN-KERNEL (green 1325, axiom-clean):** `iRK`
  gated on `zTag dᵢ = 4` (+ `iRKDef`/`iRK_defined`/invariants), `red_zK_splice` gains `htag`, new
  `red_zK_rep_nonchain`, and **`ZRegular_red_zK` is now UNCONDITIONAL** (`hseltag` dropped, `#print axioms`
  = `[propext, choice, Quot.sound]`) — the lap-94 regularity wall is cleared. Crux2Blueprint dispatch
  restructured (non-chain replace = disclosed sorry = deep validity residual). Wrote
  `ANALYSIS-2026-06-25-lap95-dispatch-fix-not-pivot.md`; refreshed STATUS + PENDING_WORK. NEXT = the deep
  validity half (`tpReduce` conclusion-reduction) + `iord_descent_red` + headline.
- **2026-06-25 (lap 92 — DEEP REFLECTION):** Re-verified kernel (green 1325, headline 0 math axioms, faithfulness
  anchor clean, statement re-audited vs paper — no drift). **Direction KEPT; recommended a sub-route PIVOT.**
  Diagnosed the laps-78–91 stall as an *artifact of the finitary-eigenvariable presentation*: route A refuted
  (lap-90), route B `tpReduce` still needs validity-preserving eigenvariable substitution (O2/lap-78), no
  validity-free bypass (lap-90). Gathered three independent evidences that the **ω-rule** is the fix —
  Bryce–Goré's complete Coq `Con(PA)` (`PA_omega.v`, no eigenvariables), the repo's own axiom-clean meta engine
  `Zinfty.lean` (ω-rule `allω`), and Buchholz §6 `Z^∞` (embeds finitary→infinitary *to* do cut-elimination).
  The ω-rule *selects* the witness premise `dₙ` instead of substituting ⟹ dissolves O1+O2+`tpReduce`. NEXT:
  a `wip/InternalZomega.lean` de-risk spike before the rebuild. STOP the finitary `tpReduce`/`Zsubst` thread.
  See `REFLECTION-2026-06-25-lap92.md`. (No proof code committed this lap — synthesis is the deliverable.)
- **2026-06-25 (lap 89 — FRESH-MIND REVIEW):** Re-verified kernel (real `#print axioms`, green 1325): headline
  `[propext, sorryAx, choice, Quot.sound]` (0 math axioms). **Direction KEPT.** ⭐ **Found the lap-88 handoff
  missed a major simplification:** `peano_not_proves_consistency` is now **axiom-clean** —
  `PA_delta1Definable` was discharged UPSTREAM (Foundation proves `𝗣𝗔.Δ₁` as a `noncomputable instance`,
  `InductionSchemeDelta1.lean:1379`; no longer an axiom). The entire lap-74/78/81 second front (`src/PADelta1.lean`
  Δ₁-recognizer campaign) is moot. ⟹ **headline endgame is single-front:** only `goodstein_implies_consistency`
  (`Reduction.lean:68`) remains = crux-2 = `redSound`. Refreshed STATUS header / Where-it-stands / Outstanding /
  ledger off the stale lap-78 "two fronts, ladder blocked at rung 1→2" framing onto the lap-88 dispatch-assembly
  reality (all three case-5 branches object-complete; remaining = tag-4 dispatch + `redSound`).
- **2026-06-25 (laps 79–88 — crux-2 dispatch branches brought to OBJECT-completeness):** After lap-78 found the
  `zsubst`/criticality ladder architecture-blocked, the work pivoted to the lap-86 finding (`not_zKCritical_red_zK`,
  in-kernel): the critical-only `red` is itself non-critical after one step ⟹ tag-4 MUST dispatch Buchholz cases
  5.1/5.2.1/5.2.2. Laps 82–88 then built each branch's reduct OBJECT with co-located validity (`zKValidF`) +
  descent (`iord_*`) + `ZDerivation` constructor: **5.2.2** `iCritAux` + `ZDerivation_iCritAux_of_zK` +
  `iord_descent_iCritAux` (lap 86); **5.2.1** the genuine ordered-insert `seqInsert` + `zKValidF_seqInsert` +
  `ZDerivation_seqInsert_of_zK` + `iord_descent_seqInsert'` (rank-general, laps 87–88); **dispatch index**
  `permIdx` + `permIdx_lt_of_not_zKCritical` (lap 88); `zKCritical` made Δ₁ (lap 86). All axiom-clean
  `[propext, choice, Quot.sound]`, build green 1325.
- **2026-06-24 (lap 78 — FRESH-MIND REVIEW):** Found the crux-2 rung-2 plan is **architecture-blocked**, not a
  one-lap freshness add: `ZDerivation_zsubst` cannot preserve `zKValid` criticality (a formula-*inequality*)
  under numeral substitution (`fvSubst` non-injective) — two explicit counterexamples, one defeating even full
  Buchholz regularity. Fix needs a deep-reflection redesign (recommend structural/index-based criticality).
  `ANALYSIS-2026-06-24-lap78-criticality-substitution-wall.md`. **Pivoted to the mandatory 2nd front
  `PA_delta1Definable`**: landed `paMinusDelta1 : 𝗣𝗔⁻.Δ₁` axiom-clean (`Theory.Δ₁.ofFinite`) + `paDelta1 :
  𝗣𝗔.Δ₁` assembly; isolated the whole wall to `inductionSchemeUnivDelta1 : (InductionScheme ℒₒᵣ Set.univ).Δ₁`
  (`src/GoodsteinPA/PADelta1.lean`, one disclosed `sorry` + construction plan). Green 1324; headline unchanged
  (`[propext, sorryAx, choice, Quot.sound]`), not wired (anti-fraud). `55f30af`.
- **2026-06-24 (lap 74 — DEEP REFLECTION):** Altitude pass on the stronger model (`REFLECTION-2026-06-24-lap74.md`,
  primary deliverable). Re-verified the kernel (real `#print axioms`, green **1323**): headline 0 math axioms,
  honest `sorry`, anti-fraud intact; statement re-audited faithful (no transcription drift — `goodsteinSentence`
  = standard Goodstein over genuine `Peano`). **Direction KEPT + re-validated.** Three sharpenings: **(1)
  PROVED crux 2 is unavoidable** — the banked free-X monument is the wrong shape and the specific-instance route
  still needs Gentzen, so no ε₀-strength-free proof exists (closes the "resurrect the monument" door for future
  laps). **(2)** flagged the lap-70 reduct re-work (genuine reduct re-fits validity AND descent; `iord`/ω-tower
  *assignment* reusable, `iR2`/`iCritReduct` *definition* + iterate-descent *assembly* superseded — stop
  extending `iR2`). **(3)** named `PA_delta1Definable` the official second front (still an upstream `axiom`,
  mandatory, untouched). Laps 71–73 (rung 0.5 + `zsubst` define/correctness) confirmed monotone, not circling.
- **2026-06-24 (lap 71 — FRESH-MIND REVIEW):** Re-verified the kernel from real `#print axioms` (headline
  0 math axioms, honest `sorry`; lap-70 landmarks clean; build green 1321). **Direction KEPT.** Crux 2 is
  localized to the single `RedSound` obligation; lap 70 refuted Option B in-kernel (`not_zKValid_iCritReduct`)
  and forced Option A (genuine cut-formula-shape-dispatched reduct, cross-checked vs Bryce–Goré). Refreshed
  STATUS header / Where-it-stands / ledger off the stale lap-59/62 framing. Drove rung 0.5 (`ZPhi`
  rule-faithfulness prereq for the genuine reduct). See `HANDOFF-2026-06-24-lap70.md`.
- **2026-06-24 (laps 60–70 — crux-2 ordinal engine + RedSound localization):** Built the V-internal
  Buchholz-Z apparatus in `src/InternalZ.lean` (promoted from `wip/` lap 66, green-gated): Fixpoint
  `ZDerivation`, the `iR`/`iR2` reduction, the ordinal assignment `idg`/`iõ`/`iord`, and the **tag-4 K-case
  descent `iord_descent_iR2_zK_of_valid`** (lap 67, axiom-clean — `o(iR2(zK …)) ≺ o(zK …)` for a valid `K^r`
  chain). Lap 70 **refuted Option B in-kernel** (`not_zKValid_iCritReduct`: the ordinal-faithful `iR2` can't
  preserve `zKValid`) and forced **Option A** (genuine validity-preserving reduct); banked the rule-inversion
  peeling primitives (`zDerivation_zIall_inv`/`_zIneg_inv`/`_zAxAll_inv`/`_zAxNeg_inv`/`_zAtom_inv`), the clean
  I-rule `RedSound` fragment (`ZDerivation_iR2_zIall`/`_zIneg`), `isChainInf_of_last`, and the rung-0.5 start
  (`zIallWff`/`zInegWff` premise-sequent conditions). Lap 62 deep reflection hardened the endpoint to
  axiom-free-or-abandoned and surfaced the C0.5 Foundation→Z bridge.
- **2026-06-24 (lap 59 — FRESH-MIND REVIEW: natural-sum order foundations; ORDER>iC reprioritization):**
  Re-verified the kernel from real `#print axioms` (headline `[propext,sorryAx,choice,Quot.sound]`, 0 math
  axioms; `goodstein_implies_consistency` = +`PA_delta1Definable`; build green 1318). Continued the lap-58
  crux-2 brick `wip/InternalNadd.lean` (Hessenberg natural sum `#` for Buchholz's `õ`). **Banked (all `lake
  env lean` green, axiom-clean):** `isNF_insTerm` + `isNF_inadd` (NF preservation, order-induction through
  the three `insTerm_ocOadd` branches); `insTerm_prepend` (prepend when the new exp dominates) +
  `inadd_zero_right` (`#` right-unit on NF); `thenV_one_right` + `icmp_omega_pow` (`ω^·` is an
  order-embedding: `icmp(ω^α)(ω^β)=icmp α β`); `inadd_omega_pow` (`ω^α # b = insTerm α 1 b`, the õ
  left-fold step). **Reprioritization (recorded `PENDING_WORK` lap-59):** the §4 descent consumes `#`'s
  ORDER, not `iC`; and `iC_inadd ≤ iC a+iC b` does NOT follow from the naive fold (needs the NF
  leading-exponent structure). ⟹ strict `#`-monotonicity + commutativity/associativity on ω-power
  summands is the next deep target; `iC_inadd` deferred. Crux 1 untouched (still the tractable milestone).
- **2026-06-23 (lap 56 — FRESH-MIND REVIEW: crux-1 redirect, natCode↔NF bridge dissolved):** Re-verified
  the kernel (headline `[propext,sorryAx,choice,Quot.sound]`, 0 math axioms; `goodsteinSentence_faithful`
  clean; M1+Phase 1 done; build green 1315). Validated direction (crux 1 = right hardest-but-tractable
  target; crux-2 eq-5 stays 🟠). **Two crux-1 findings, both acted on** (`wip/GentzenCon.lean`, `lake env
  lean` green; memory `prwo-transparent-icmp-not-opaque-precphi`): (1) lap-55 built `prwoInstance` on the
  OPAQUE `precφ` (`codeOfREPred₂`, std-only spec) → wall-B opacity in nonstandard `M`; REBUILT on the
  transparent `prec_internal`/`icmp` (mirrors lap-36) ⟹ natCode↔NF order bridge **DISSOLVED**,
  `prwoInstance_faithful` shed its F-φ `native_decide` artifact (now axiom-clean). (2) `nonterminating_of_
  seq_descent` for *arbitrary* seq is unprovable on the standard girder (`F_diag_not_dominated`) — the real
  remaining content is a standard-level domination certificate from the `seq` descent, discharged at
  `gentzenDescentφ`; named as the concrete next-lap target. Laps 54–55 (lap-55 collapsed crux 1 to the one
  bridge via the per-model `provable_of_models` route; lap-54 iF growth bricks) folded in; STATUS/ledger refreshed.
- **2026-06-23 (lap 53 — DEEP REFLECTION: route re-derived from source, honest endpoint named):**
  Altitude pass. **Re-derived the lap-46 route decision from the mathematics** (not the summaries) and
  KEPT it: Goodstein⟹PRWO(ε₀), not free-X-TI (§3 Grzegorczyk domination is primrec-only, so the free-X
  bridge is the *wrong implication direction*, not merely hard). Re-verified the kernel (headline 0 math
  axioms; faithful bridge clean; `goodstein_implies_consistency` already carries `PA_delta1Definable`
  through its type) and traced the headline statement to audited `goodsteinSeq` — no drift. **Two honest
  re-classifications:** (1) the cruxes have ASYMMETRIC feasibility — crux 1 is 🟡 tractable (~80% built,
  a few laps to assembly), crux 2 is 🟠 GENERATIONAL (confirmed at source: Foundation's `Hauptsatz.main`
  is meta-level, no arithmetized ordinal analysis upstream, the Thm-5.6 monument can't be reused) and
  settled as a cited eq-(5) axiom; (2) the realistic HONEST ENDPOINT = crux-1 built + crux-2 cited eq-(5)
  + `PA_delta1Definable` upstream, best-case headline `[propext, choice, Quot.sound, PA_delta1Definable]`
  — flagged the DIRECTION-rule-#1 tension for operator reconciliation. **Direction KEEP** (drive crux-1 to
  `goodstein_implies_prwo` assembly; chip crux 2 only opportunistically). Build green 1313 jobs; headline
  `sorry` intact. See `REFLECTION-2026-06-23-lap53.md`.
- **2026-06-23 (lap 50 — REVIEW + crux-2 PRWO formulation built & faithfulness-certified):** Fresh-mind
  pass. Validated direction (Route A, KEEP) against the real kernel (headline honest `sorry`, 0 math
  axioms, 1311 jobs). Confirmed crux-1 step-3 (internal `ig` f-recursion → internal Grzegorczyk `F`,
  Ackermann) is **blocked on infra Foundation lacks** ⟹ followed the lap-49 handoff's recommendation and
  advanced the *unblocked* **crux 2** (Gentzen `PRWO→Con`). Mapped Foundation's substrate (Explore):
  **NO universal evaluator / Kleene-T** ⟹ PRWO must be a **per-formula schema** (memory
  `crux2-prwo-schema-no-universal-evaluator`). Built `wip/GentzenCon.lean` (type-checks, 2 disclosed
  crux sorries): **`prwoInstance seq := “¬∀ n y z, (!seq y n ∧ !seq z (n+1)) → !precφ z y”`** — reuses the
  existing ε₀-ordering formula `SeamDefinability.precφ` (no `isNF` needed; `natCode` bijects onto all CNF).
  **`prwoInstance_faithful` PROVED** (std-model ↔ meta-PRWO; axioms = trust base + 1 🟢 F-φ native_decide —
  the formulation is kernel-certified faithful). Also proved `gentzenDescent_descends`/`derivesEmpty_iterate`
  + the assembly `goodstein_implies_consistency_via_gentzen` (crux1∘crux2 = the `Reduction.lean` interface,
  types validated). Deep cores left as cited sorries: `ord`/`R`/eq-(5) (Buchholz [6]) — Foundation's
  Hauptsatz is meta-level only, no shortcut. `src/` untouched (anti-fraud); build green 1311 jobs.
  **⭐ KEY INSIGHT (post-commit):** the schema realization collapses **crux 1's internal-Ackermann wall**
  (laps 45–49) — the headline composes crux 1 at the SINGLE concrete primrec instance `gentzenDescentφ`,
  so Lemma 3.2 (`rathjen.txt:401`) gives a **STANDARD** Grzegorczyk level, NOT internal. ⟹ crux 1 is
  downgraded from generational to tractable standard-level internalization (reuse the abandoned
  `ibigMul` lead + ℕ-template `Grzegorczyk.lean`); **THE remaining hard wall is now crux-2 eq (5)**
  `ord(R d)≺ord d`. Memory `crux1-headline-needs-only-standard-level`; unbuilt — validate before relabeling.
- **2026-06-23 (lap 47 — REVIEW + internal Thm 3.5 COMPLETED):** Validated the lap-46 route resolution
  against the real kernel (headline honest `sorry`, 0 math axioms; `peano_not_proves_TI` clean; Gödel-II
  surface carries `PA_delta1Definable`). Direction **KEEP** (Route A = Rathjen Cor 3.7). Landed the one
  remaining piece of internal Thm 3.5: **ω-tower cofinality** `iwtower_cofinal : ∀ c, ∃ s, c ≺ ωₛ`
  (`InternalThm35`, axiom-clean) — proved with NO NF hypothesis (the comparison `icmp_ocOadd_lt_exp` reads
  only the leading exponent, so `sigma1_order_induction` at `ocExp c < c` decides the whole code). This
  discharges `bbeta_desc`'s seam hypothesis `hbdry` ⟹ `bbeta_desc_exists` produces the full descending
  Thm 3.5 sequence unconditionally. **Internal Thm 3.5 is now hypothesis-free.** Re-framed STATUS header /
  Where-it-stands / Outstanding / ledger off the stale free-X framing onto Route A. Build green 1311 jobs.
- **2026-06-23 (lap 46 — ROUTE RESOLVED):** Settled lap-45's fork → **Route A** (Rathjen Cor 3.7:
  γ→PRWO(ε₀)→Con(PA)→Gödel II), grounded in Rathjen 2014 Thm 2.8 + §2-3 (`scratchpad/rathjen.txt`). The
  free-X β-wall (`DescentSemantic:582`) is the WRONG target: §3 is primrec-only (machine-checked obstruction
  `not_dominated_of_diag_le`), but a PRWO descent is *internally* primrec ⟹ Lemma 3.2 applies. Decomposed
  `goodstein_implies_consistency` faithfully in its docstring (2 girders). Built the model-internal Thm 3.5
  block-tail + ω-tower + full `bbeta` sequence (`InternalThm35.lean`, axiom-clean) modulo the cofinality
  input now discharged lap 47. Memory `route-resolved-prwo-gentzen`.
- **2026-06-23 (lap 44 — DEEP REFLECTION):** Altitude pass on the stronger model. Re-verified kernel from
  real `#print axioms` (headline 0 math axioms; `peano_not_proves_TI` clean; chain = trust-base + 🟢
  native_decide + 1 `sorryAx`); re-grounded Rathjen §3 slow-down against the PDF (subagent). **Direction
  KEEP.** Two findings (`REFLECTION-2026-06-23-lap44.md`): **(A)** the wall's literal `sorry`
  (`DescentSemantic.lean:574`) routes through the **dead, unachievable 𝚺₁ path** (`hbound`+
  `nonterminating_internal`; `b` is X-dependent so `𝚺₁-Function₁ b` is FALSE in general) — the X-essential
  `nonterminating_of_xDescent` (built lap 41) is the correct consumer, **rewire to it** (reduces the wall to
  the honest "produce `β : M→M`" obligation). **(B)** `Grzegorczyk.lean` collapses Rathjen's length-`|·|`
  Lemma 3.3/Cor 3.4 onto **C** (C-based widths) — self-consistent on paper but UNVERIFIED until the ℕ Cor
  3.4 assembly typechecks; finish it (de-risk) before M-internalizing. Trajectory (30→43) = genuine forward
  motion, not circling. Build green 1309 jobs; STATUS + ledger refreshed; headline `sorry` intact.
- **2026-06-23 (lap 39 — review):** Fresh-mind pass. Real `#print axioms` reconfirmed: headline =
  `[propext, sorryAx, choice, Quot.sound]` (0 math axioms), girder `peano_not_proves_TI` clean, faithful
  bridge clean; the lone `sorryAx` traces to `hbound` (`DescentSemantic:416`). Direction **re-validated**:
  the lap-38 decomposition (internal `evalNat_succ_base` → `ineq6_step` → seam rewire → βₖ) is the correct,
  highest-value attack on `hbound`. Fixed stale `HANDOFF.md` symlink (→ lap38). Began grinding internal
  `evalNat_succ_base` (digit-peel lemmas + structural induction on the substrate). Aristotle available, idle.
- **2026-06-23 (laps 37–38 — internal-ONote substrate COMPLETE):** Built the ε₀-notation arithmetic *inside
  `IΣ₁`* in `InternalONote.lean` (sorry-free, axiom-clean): `icmp` (CNF comparison via pair-indexed CofV
  table), `isNF` (CNF well-formedness as a 0/1 product flag — no negated existentials), and **the crux**
  `ievalNat_lt_of_icmp_eq_zero` (Rathjen 2.3(iii) order-reflection), proved **digit-direct** (no ordinals, so
  it internalizes) via a combined tail-bound + monotonicity strong induction (`evalNat_reflect_combined`).
  Substrate inventory: codes/`iC`/`ievalNat`/`iCanon`/`icmp`/`isNF`/order-reflection. Aristotle `ibump_mono`
  COMPLETE (downloaded, not yet ported to V — order-reflection didn't need it). Build green 1307 jobs.
  *(Older bullets laps 21–38 trimmed lap 74; see git history, dated HANDOFFs, and the lap-36/44/53/62
  reflection docs. Arc: laps 21–35 assembled the free-X Thm 5.6 monument + the model-internal descent
  scaffold; lap 36 dissolved wall B [transparent `goodsteinSentence`]; lap 45→46 resolved the route to
  Route A [Goodstein⟹PRWO⟹Con], retiring the free-X back-end as off-path.)*

## Outstanding
**Route A = Rathjen Cor 3.7 (resolved lap 45→46).** The headline reduces (axiom-clean) to
`Reduction.goodstein_implies_consistency : 𝗣𝗔⊢γ → 𝗣𝗔⊢Con(𝗣𝗔)`, a disclosed `sorry` = two deep girders.

### Short-term (mirror PENDING_WORK top) — crux 2 = drive `false_of_ZDerivesEmpty` to 0 sorries (the {3,4} core is DONE)
**⭐⭐⭐ Lap-161 CURRENT (DEEP REFLECTION; supersedes the lap-158 block — its "degree-induction design spike FIRST"
mandate is STALE: the spike was DONE at lap 158 and REFUTED its own hypothesis; the {3,4} producer is CLOSED).**
Crux-2 termination (M1b-term) is the existence-form / constructive-`GenReductCert` pivot. **The {3,4}-producer
cut-reduction — the deep core (Buchholz Thm 2.1) — CLOSED in-kernel** at laps 158-160: `repProducerClose`
(`Crux2Blueprint:3455`) `:= Or.inl (certReplace_of_premise_cert … (IH m …))`, non-sorried, consumed in the live
dispatch at `:3578-3581`. Headroom is LOCAL to each flatten (premise's own `irk+1 ≤ idg(premise)`), NOT the chain's
degree — so NO outer degree-induction (the lap-158 spike `9ac1bf3` refuted that). **What remains = the STRUCTURAL
escape set + the port + gDef.** Six live sorries, NOT independent:
1. **`genReduct_chain_noRedex_anySucc`/`residual`** (`:3407`/`:3451`) — the lead domino. Reached ONLY for: (i)
   **⊥-exit ex-falso** — a tag-0/7 leaf or tag-5 escape puts `⊥∈Γ`/`^∀⊥∈Γ`; `⊥∈Γ ⟹ Γ→C` has NO single Z-rule
   (the lone ex-falso `zAxNeg` needs a `¬q,q` pair, not bare `⊥`) — needs an internal **⊥-elim/weakening** lemma
   (the ONE genuinely-new piece); (ii) **C-exit R-intro replay** (tag-1/2 major produces the conclusion succedent
   `C`); (iii) **tag-5/6 thread-escape** (shared with `axMajorResidual` — prove once via a factored
   `threadEscapeClose`).
2. **`ind_reduct_anySucc`** (`:3382`) + **`genReduct_chain_hasRedex_anySucc`** (`:3391`) — the other two anySucc
   leaves (off-`⊥` generalization). hasRedex_anySucc: ∀-redex = clean port (`certFlatten_of_critHalves` off ⊥);
   ¬-redex = the `keepTip` (genuinely needs the ⊥-exit, lap-159). ind_reduct_anySucc: `k`-fold unfolding
   `⟨d0,d1[a:=0..k-1]⟩`, `k=⟦t⟧` (check `zIndWff` admits a closed-`C` zInd).
3. **COLLAPSE (do NOT attack standalone — they DROP FROM the port):** once leaves 1-2 close, `genReduct_botSucc`/
   `genReduct_anySucc` become thin wrappers that DROP `axMajorResidual` (`:3735`) AND its Γ=∅ twin
   `descent_step_K_noncrit_axMajor` (`:4180`, same content). One ex-falso lemma + the port collapses FOUR of six.
4. **gDef `exists_sigma1_descending_step`** (`:4309`) — the separable fifth. Σ₁-definable step function; NOT μ-min
   (wrong polarity, refuted lap-139). Route: primrec WITNESS BOUND `∃ d' ≤ B(w)` on the reduct code
   (`wip/WitnessBound.lean`) OR make the constructive `genReduct` reduct a definable function. AFTER the residuals close.
**NEXT (highest-value):** build the internal **ex-falso/weakening** lemma (standalone, mirror `leafCloseC`/
`axNegCloseGen` cert shape at `:3462`/`:3473`), wire it to close `residual` (:3451) → the first whole-lemma DROP since
lap-153/154. FORBIDDEN: re-spiking the {3,4} producer / outer degree-induction (DONE + refuted); `red` witnesses;
`iord`-recursion for the construction; `redLeast` for gDef; the refuted single-premise `seqUpdate` splice; #3/#4
standalone before the port; M2/M3/M4. **(ALTITUDE: M2 = Foundation→Z embedding bridge, ~0% built + crux-entangled,
is the NEXT horizon AFTER `false_of_ZDerivesEmpty` closes; `goodstein_implies_consistency` `Reduction.lean:68` is a
bare sorry NOT YET wired to `false_of_ZDerivesEmpty` — "only the crux left" ≠ "almost done.")**

**⭐⭐ Lap-107 CORRECTION (HISTORICAL — the whole `red`-engine-redesign program below is RETIRED by the
existence-form pivot, lap 132→144; kept for provenance only).** Two
kernel-verified findings: `ZInf.allInv` is VACUOUS (one-weakening proof; `ZInf : V → Prop` has no ordinal +
keeps `^∀φ`), and external Lean inductives (`ZInf`/`ZcOK`/`ZcDer`) are non-load-bearing (the headline needs
the descent in EVERY `V ⊧ IΣ₁` incl. non-standard models, where no external derivation tree exists for the
non-standard coded ⊥-proof ⟹ `foundation_bot_to_Z_empty` is unprovable). The load-bearing carrier is the Σ₁
engine `red`/`iord` (`InternalZ.lean`). THE crux (re-confirmed lap-104): engine `red` via `iRNextG`
dispatches only on the top `zTag`, so after one K/cut reduction it stalls ⟹ `iord_descent_red`
(`Crux2Blueprint.lean:533`) is unprovable for the current `red`. **NEXT (hardest-first):** (1) redesign
`red`/`iRNextG` to locate + key-reduce the lowest cut anywhere in the ∅→⊥ derivation code (Σ₁ tree-search;
the prototype inversion cases are the combinatorial GUIDE — which premise/witness, how `#`/`iotower` ordinals
combine); (2) prove `iord_descent_red` (K case) for the redesign; (3) `false_of_ZDerivesEmpty` via the
`iord`-descent + PRWO; (4) discharge the `Crux2Blueprint` validity `sorry`s + the embedding, then wire
crux-1 ∘ crux-2 → `Reduction.goodstein_implies_consistency` → headline (only when `#print axioms` clean).
The prototypes stay as a sketch — no further investment.

**⭐ Lap-104 CORRECTION (historical — supersedes the lap-95 finitary dispatch-gate plan below).** Crux 1 DONE axiom-clean
(lap 57); `PA_delta1Definable` discharged upstream (lap 89). The crux-2 route is **Path C** (ω-rule, stored
ordinals; the finitary `redZKReady` motive is retired/likely-broken). Lap 102→103 landed the Path-C node
bricks (ω-∀, ω-ind, cut, ∃) + `sord` (Σ₁-def) + per-step ordinal drops, and packaged the endgame as
`red_iterate_descends` (`hinv`/`hdrop`/`hz`). **Lap-104 in-kernel certificate: the naive dispatch-shaped `P`
fails `hinv` — the ∀/∃-cut reduct's premises are substituted engine derivations (tag ≤ 6), not principal
ω-nodes, so `red` stalls.** Corrected attack path, hardest-first:
1. **Build the Path-C derivation predicate (the datatype).** A small isolated Σ₁ `Deriv`-style predicate
   `zcOK d` (template: `InternalZ`'s `PR.Blueprint`/`Construction` Fixpoint; rule set: `ZinftyF.Deriv`)
   recognizing the ω-node shapes {ω-∀, ω-ind, cut, ∃, ∧, ∨, atom-axiom}, each storing its ordinal; validity
   = premise codes well-formed + `∀ premise, sord(premise) ≺ sord(node)`. This is the bottleneck — `hinv`,
   the embedding, and arithmetization all need it. ~1k+ line, multi-lap.
2. **Inversion operators** `redInv∀`/`redInv∧`/`redInv∨` over `zcOK`: from a derivation of `Γ, A` extract a
   derivation of the immediate subformula instance with stored ordinal `≼`. ∀-inv on the ω-∀-node is premise
   selection (banked `zAllOmega_cut_valid`); the general case recurses through the last rule (Schütte). These
   are what `red` calls to RE-PRINCIPALIZE the cut reduct's premises — the genuine content of `hinv`.
3. **`red` (Buchholz Def 3.2) with inversion** + `hinv` (`red` preserves `zcOK` ∅→⊥) + `hdrop` (per-step
   stored-ordinal drop, bricks 1/3 + inversion ordinal bounds) → `red_iterate_descends` with the GENUINE `P`
   = `zcOK`-⊥-derivation.
4. **Embedding** (M2 analogue): a Foundation/`ZDerivation` ⊥-proof yields a `zcOK` ⊥-derivation `z` (`hz`).
5. **Arithmetize** `red` + `gentzenDescentφ` (Σ₁ graph of `n ↦ sord(red^[n] z)`) → discharge
   `gentzen_descent_of_inconsistent` (`wip/GentzenCon.lean`) via the V-internal descent + crux-1 PRWO. Then
   wire crux-1 ∘ crux-2 → `Reduction.goodstein_implies_consistency` → headline (only when `#print axioms`
   clean — anti-fraud).

#### (SUPERSEDED lap 102/104 — finitary Path-X plan, kept for provenance) crux 2 = `redSound`, the SURGICAL dispatch gate
Crux 1 (`γ→PRWO`) DONE axiom-clean (lap 57). `PA_delta1Definable` DISCHARGED UPSTREAM (lap-89 finding —
Foundation proves `𝗣𝗔.Δ₁`). **Single open headline obligation = `goodstein_implies_consistency`
(`Reduction.lean:68`) = crux-1 ∘ crux-2 = `redSound`** (internalized cut-elimination). **Lap-95 sharpening:
O2 (eigensubst `ZDerivation_zsubst`) DONE; O1 (`ZRegular`) DONE except `ZRegular_red_zK`'s lone false
hypothesis `hseltag`. The wall = the `iRK` splice dispatch mis-firing on non-chain selected premises.**
1. **Port the gate** (de-risked `wip/InternalZdispatch.lean`, lap 95): rewrite `iRK` (`InternalZ.lean:6108`)
   to splice only when `zTag dᵢ = 4 ∧ ¬ permIdx dᵢ < lh(zKseq dᵢ)` (= dᵢ a critical chain); route non-chains
   to the replace `iRKr` (Buchholz Def 3.2 case 5.2.2). Update `iRKDef`/`iRK_defined` (add the `zTag dᵢ=4`
   conjunct, mirror `iRKDef`); re-prove invariants (`split_ifs <;> simp`). Fix dependents: `red_zK_rep`/
   `red_zK_splice` hyps (`Zsubst.lean:1654/1669`), DROP `hseltag` from `ZRegular_red_zK`, and the compiled
   `Crux2Blueprint.lean` `ZDerivation_red_zK_dispatch`. `iord`-descent lemmas are NOT in the radius
   (per-branch facts on `iRKs`/`iRKr`/`iRKc`; `iord_descent_red` still open). Green `lake build`.
2. **Validity half** (the deep residual): rewire the replace branch to emit `tpReduce (tp dᵢ) Π n`
   (`InternalZ.lean:1064`, Σ₁-def'd); prove `ZDerivation_red_zK_rep`/`_splice`/`_crit` (Crux2Blueprint
   sorries) on the reduced conclusions (lap-90: keep-Π `red` faithful only for `tp = Rep`).
3. **`redSound`** = the combined induction `ZDerivation d → ZRegular d → ZDerivation (red d) ∧ ZRegular (red d)`;
   then `iord_descent_red` (`Crux2Blueprint:306`) → `false_of_ZDerivesEmpty` → `Reduction.lean:68`. M2
   (`foundation_bot_to_Z_empty`, the C0.5 Foundation→Z bridge) + M3 remain as `Crux2Blueprint` leaves.
   Then, only if `#print axioms` is clean, discharge the headline `Statement.lean:22`.

### Long-term / banked
- **Internal Thm 3.5 — COMPLETE (lap 47), route-independent.** `InternalThm35.bbeta_isNF`/`bbeta_C_le`/
  `bbeta_desc_exists` + `iwtower_cofinal`. Survives any route change; consumed by Lemma 3.6.
- **`peano_not_proves_TI` (Buchholz §5, Thm 5.6) — axiom-clean but OFF the headline path.** Free-X-TI ⊢ PRWO
  (wrong direction), so it cannot chain to Con(PA). A banked monument (M4 `embedC` + M5 `cutElim` + Boundedness
  + C₁/C₂/D/F-φ). Do NOT try to wire it to the headline. The free-X β-wall (`DescentSemantic:582`) is the
  abandoned target — a `wip/` candidate (machine-checked OFF-path by `not_dominated_of_diag_le`).
- **Witness-bounded cut-elim** (`wip/{Bounded,Split,Operator}Zinfty`) + **M6 Hardy lower bound** — older banked
  threads, off-path. Never delete.

### To completion
Headline discharged ⟺ crux-2 (`redSound` = Gentzen Thm 2.8 `PRWO→Con(PA)`, internalized cut-elimination)
lands and chains through `goodstein_implies_consistency`, AND `#print axioms peano_not_proves_goodstein` is
`[propext, Classical.choice, Quot.sound]`. **Lap-89 simplification:** the former Route-A honesty caveat
(Gödel II riding the upstream `PA_delta1Definable` axiom) is **GONE** — Foundation discharged
`PA_delta1Definable` into a proven instance, so `peano_not_proves_consistency` is already
`[propext, choice, Quot.sound]`. **⚠️ Lap-152 honest scoping (judge-flagged):** "single-front" is true for
the *upstream-axiom* picture, but crux-2 itself has TWO bodies of work — **(i) M1b-term**, the internal
`false_of_ZDerivesEmpty` termination (the current focus: the `genReduct_botSucc` code-recursion, 2 master-key
sorries + gDef), and **(ii) M2**, the Foundation→Z bridge (`Z`-derivation ↔ Foundation sequent calculus,
ordinal-assignment soundness, the `InternalPRWO` discharge from crux-1) — which is ~0% built and
crux-entangled. Headline discharged ⟺ BOTH land and chain through `goodstein_implies_consistency`, with
`#print axioms peano_not_proves_goodstein` = `[propext, Classical.choice, Quot.sound]`. Do NOT read "only the
crux is left" as "almost done": M2 is the next horizon after M1b-term, and warrants its own scoping lap.

## Axiom ledger (per headline / landmark theorem — the fidelity spine)
| theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `peano_not_proves_goodstein` (headline, `Statement.lean`) | uncond. (Kirby–Paris) | `propext, sorryAx, Classical.choice, Quot.sound` (**lap-107 real, re-verified in-kernel `lake env lean`**) | 🔓 open `sorry` (LOCKED, anti-fraud) — **0** math axioms; `sorryAx` traces the lone math `sorry` `goodstein_implies_consistency` = crux-2. Route A: reduces (axiom-clean) to `goodstein_implies_consistency` via `not_proves_of_implies_consistency` + Gödel II. **⭐ Lap-107 DIRECTION CHANGE:** the lap-102→106 external-inductive prototypes (`ZInf`/`ZcOK`/`ZcDer`) are a DEAD END — `ZInf.allInv` is VACUOUS (kernel-verified: one-weakening proof, ignores `ht` + membership; `ZInf` has no ordinal index + doesn't erase `^∀φ`, so it's a weakening of the META `Zinfty.allInvAux`'s ordinal-preservation+erasure content) AND external inductives can't carry a non-standard-code descent (so `foundation_bot_to_Z_empty` is unprovable on them). The load-bearing carrier is the Σ₁ engine `red`/`iord`; THE crux is that engine `red` (via `iRNextG`) dispatches only on the top `zTag` ⟹ stalls after one K-reduction (lap-104) ⟹ `iord_descent_red` unprovable for current `red`. FIX = redesign `red` to find+reduce the lowest cut anywhere in the ∅→⊥ code. Multi-month. Statement re-audited vs paper (genuine hereditary base bump) — no drift. **⭐ Lap-111 DEEP REFLECTION (re-verified in-kernel, 0 math axioms):** direction KEPT. The lap-107 "stall" defect = a SELECTION bug (`red d = d` at axiom-leaf selections); it re-surfaces as the `iord_descent_red` fixpoint branches (`Crux2Blueprint:568/610/612` + the `:594` chain-REPLACE IH false-at-fixpoint). **Highest-value lever:** reformulate `iord_descent_red` → disjunctive `red d = d ∨ iord ≺` and `false_of_ZDerivesEmpty` → "terminate-at-cut-free ⟹ absurd" — fixpoint branches close trivially, obligation sharpens to `red d=d ⟹ cut-free` + `no cut-free ∅→⊥`. Then lap-110 cut-formula strip (`hr'`), then the ∀/¬-INVERSION on the engine (`ZDerivation_red_zK_crit`; the genuine cut-elim content, ≈0% done, only attempt `ZInf.allInv` killed vacuous lap 107; template `Zinfty.allInv`). See `REFLECTION-2026-06-25-lap111.md`. **⭐⭐⭐ Lap-120 DEEP REFLECTION (re-verified in-kernel, 0 math axioms):** the INVERSION is now SOLVED (laps 112–119 proved critical-cut soundness both polarities, Buchholz §5). But that was reduct SOUNDNESS, not termination. **The genuine open crux = the SELECTION/STALL defect:** `false_of_ZDerivesEmpty` (bare sorry) cannot close because `red` stalls when `permIdx` selects an atom/`zAx1` premise (`iperm isymRep` unconditional) ⟹ tag-4 K-node is a non-cut-free `red`-fixpoint (repo flags it in `RedZKDescent.lean`). Lap-111's disjunctive `iord_descent_red` RELOCATED the stall into the unbuilt sorry (`Or.inl` branches), did not fix it; same defect as laps 104/107. **Highest-value next target = (A) `red w = w ∧ ZDerivesEmptyR w ⟹ False`** (fixpoint-absurdity; vacuity-of-stall first, probe `ZRegular`), NOT the atomic engine swap. See `REFLECTION-2026-06-26-lap120.md`. **⭐⭐⭐ Lap-132 DEEP REFLECTION (re-verified in-kernel, 0 math axioms; statement re-audited, no drift):** direction KEPT, faithfulness clean. The (A)/stall sub-goal that drove laps 120→131 is an ARTIFACT of the *fixed-deterministic-engine* formulation: "fixpoint ⟹ cut-free" was refuted for the permIdx engine (lap 129), forcing the whole no-stall campaign (`firstBotPrem_reducible`/`majorIdx`/tag-5/6 dispatch/`seqAntSeq` fold/ZPhi exact-shape). **Reframe the iteration to `redLeast`** = Σ₁ least *descending* reduct; then "`redLeast d = d` ⟺ no descending reduct ⟹ `d` cut-free" by the contrapositive of a single existence lemma (E) — definitional, no faithful-selector proof. (E) discharges at the ⊥-root from banked facts (`zTag_Ind_or_K_of_ZDerivesEmpty`, sound+descending K-critical/Ind reducts laps 112-119 + `iord_descent_iRKcCrit_corr`/`_zInd`, Cor 2.1). Obviates the permIdx campaign; REUSES soundness + folds (`ZRegular_red`/`ZFresh_red`) + per-reduct descent. NEXT = `wip/ExistenceEndgame.lean` spike (decisive, mirror lap-101). See `REFLECTION-2026-06-26-lap132.md`. **⭐⭐⭐ Lap-140 ALTITUDE REVIEW (re-verified in-kernel, 0 math axioms; faithfulness clean):** the existence-form pivot is now FULLY ASSEMBLED except ONE lemma. lap-135 ported the spike to src; lap-137 type-corrected the PRWO seam (`InternalPRWO V` hypothesis); lap-138 PROVED the Σ₁-orbit (B)/(B0) via `IIter.iIter`; lap-139 made the tag-5/6 critical-cut half-layer pair-parametric AND reconciled (A)≡`descent_step_K_majorIdx`. **The whole crux-2 termination = the single lemma `descent_step_K_majorIdx` (`Crux2Blueprint:1764`):** `false_of_ZDerivesEmpty` sorry-free given `InternalPRWO V` + bare-∃ step; orbit proven; (A) folds in via the concrete `redStep` (μ-min route REFUTED lap-139, wrong polarity). MANDATE (DIRECTION.md lap-140) = decompose it into per-tag {3 Ind, 4 chain, 5/6 ∀/¬-axiom} src sub-`sorry`s + assemble a banked sub-piece (tag-5/6 explicit-pair `iCritReductG` soundness; or tag-3 `isChainInf_iIndReductSeqG`) to a DROP. See `HANDOFF-2026-06-26-lap139.md`, `DIRECTION.md`. **🧘 Lap-143 DEEP REFLECTION (re-verified in-kernel, 0 math axioms; statement re-audited, no drift):** the lap-140 major-tag mandate was abandoned lap-141 (critical/non-critical split). **Finding:** crux-2 = 🟡 active frontier, but the live `false_of_ZDerivesEmpty` path STILL depends on TWO kernel-verified-FALSE sorries — laps 141-142 regressed the lap-132 existence-form pivot. `descent_step_K_critical` (:1891) witnesses the bare-`∃` step with `red` (`ZDerivesEmptyR_red` → FALSE/incomplete `redSoundGen` :1471 → kernel-FALSE `zKValidF_iIndReduct_of_zInd` :80 + open zK :1508 + kernel-FALSE `ZDerivation_red_zK_crit` :1108); the genuine red-free `ZDerivation_iRKcCrit_critical_all` (:1847, lap-142) is BANKED BUT UNWIRED (zero false-dependence dropped). **MANDATE (DIRECTION.md lap-143):** derive `ZSeqAnt_iRKcCrit`; split `descent_step_K_critical` into ∀ (wire `iRKcCrit`, drops :80/:1108 for the dominant sub-case) + ¬ (named honest `redexJ≤j0`); re-witness the Ind branch with `iIndReductSeqG`. Then the DEAD `red`-soundness sorries {:80,:1108,:1211,:1384,:1471} go provably off-path → `wip/`; live frontier = {¬-case `redexJ≤j0`, non-critical 5.2, (A) `gDef`}, all genuine, none generational. See `REFLECTION-2026-06-26-lap143.md`. **🧭 Lap-146 FRESH-MIND REVIEW (re-verified in-kernel, 0 math axioms; statement re-audited, no drift):** lap-143's mandate DONE — laps 144/145 wired the live `false_of_ZDerivesEmpty` path FULLY off `red` (`ZDerivesEmptyR_descent_step`:2270 sorry-free; ¬-case CLOSED) and cracked `descent_step_Ind` to its single real obstruction. The path's live sorries are now exactly THREE — {`descent_step_Ind`:2262, `descent_step_K_noncritical`:2139 (§5.2), (A) `gDef`:2327} — NO kernel-FALSE statement among them. Validated the `zIndWff` step-clause gap is REAL (membership :1684 vs equation base :1682) and the fix is REQUIRED for soundness; refuted the ZSeqAnt + no-cascade reframes. MANDATE = DROP `descent_step_Ind` via the focused `zIndWff` step-clause→shape ripple (descent + `p=⊥` banked). See `DIRECTION.md` CURRENT DIRECTIVE (lap-146). **🧭 Lap-149 FRESH-MIND REVIEW (re-verified in-kernel, 0 math axioms; statement re-audited, no drift):** lap-146's mandate DONE — `descent_step_Ind` DROPPED (lap 146); laps 147-148 advanced §5.2 noncritical (has-redex half PROVEN; no-redex decomposed faithfully per Buchholz §14.254a/b, tag-3 repMajor proven modulo the freshFlag residual). Crux-2 = 🟡 active frontier, now **4 disclosed `sorryAx` leaves** {tag-3 freshFlag :2974, tag-4 K-recursion :2934, axMajor 5/6 :3002, gDef :3125}, none generational, none `red`. FINDING = crux-neglect signal forming (machinery closed, the general code-recursion crux untouched; tag-3 freshFlag is the LAST leaf). MANDATE (DIRECTION.md lap-149) = DROP tag-3 freshFlag via the `zFreshNext` tag-3→`freshFlag` strengthening (mirror tag-1 I∀, exact shape of the lap-146 `zIndWff` ripple), THEN the general `Γ→⊥` cut-reduction by strong induction on CODE (leaves 2934+3002) + gDef. FORBIDDEN = `red` witnesses; `iord`-recursion for the general step. **🧘 Lap-152 DEEP REFLECTION (re-verified in-kernel: headline `[propext, sorryAx, choice, Quot.sound]` 0 math axioms; `goodsteinSentence_faithful` + `peano_not_proves_consistency` clean; statement re-audited, no drift):** direction KEPT. lap-149's mandate DONE (tag-3 freshFlag DROPPED lap 149); laps 150-151 landed the code-recursion frame `genReduct_botSucc` (Σ₁ structural induction on CODE), REFUTED the false single-premise `seqUpdate` splice in-kernel (judge-convergent), PROVED the FLATTEN engine `descent_step_K_spliceHalves`, and DROPPED the false `descent_step_K_splice` via the faithful `GenReductCert` (`certReplace ∨ certFlatten`). TRAJECTORY HEALTHY (the lap-143 banking-not-wiring/witness-with-`red` worries RESOLVED; steady crux DROPS 144→151). **KEY INSIGHT:** the four open leaves reduce to TWO master keys `genReduct_chain_hasRedex` :2989 + `genReduct_chain_noRedex` :3013, which SUBSUME the outer `axMajor` :3226 (`Γ=∅` cut-partner special case) and FEED gDef :3349 (constructive cert reduct) — do NOT attack #3/#4 standalone. MANDATE (DIRECTION.md lap-152) = DROP `genReduct_chain_hasRedex` via the zSeqAnt tag-4 `Seq (seqAnt s)` fold (`zSeqAntNext` `Zsubst:2003`, proven lap-149/146 fold shape), THEN `genReduct_chain_noRedex`. ALTITUDE CAUTION = M2 (Foundation→Z bridge) ~0% built + crux-entangled — "only the crux left" ≠ "almost done." See `REFLECTION-2026-06-27-lap152.md`. **🧭 Lap-155 FRESH-MIND REVIEW (re-verified in-kernel: headline `[propext, sorryAx, choice, Quot.sound]` 0 math axioms; faithful/consistency/`false_of_ZDerivesEmpty` clean; statement re-audited, no drift):** lap-152's mandate DONE — MASTER KEY #1 `genReduct_chain_hasRedex` DROPPED (lap 153), #2 `genReduct_chain_noRedex` 6/8 branches PROVEN (lap 154). The whole M1b-term termination crux is now the SINGLE open leaf `axMajorClose` (`Crux2Blueprint:3418`, tag-5/6 L-axiom cut-partner). **COURSE-CORRECTION** off the lap-154 handoff's "(b) = lap-136 general-succedent reduct": kernel-grounded that the cut formula is `^∀⊥` (`p=⊥` via `zAxAllSuccWff`+`eq_falsum_of_substs1_falsum`) and `hnolow` forbids *creating* `^∀⊥` below j0 (a direct R-intro `zIall` would `isRedexPair` with jstar — VERIFIED `isRedexPair:4820` fires on `(zIall ^∀p, zAxAll ^∀p)`), so `^∀⊥` only threads from Γ. MANDATE (DIRECTION.md lap-155) = the SUCCEDENT-THREADING COLLAPSE (2 reusable ordinal lemmas + sub-case (a) `axLeafClose` via fresh `zAxAll s ⊥ k'` + generalize `majorPrem_*_cutPartner` off `seqAnt s=∅`; collapse (b) via leaf-threading/`hnolow`/zK-recurse), NOT lap-136 (tested first, most likely obviated). See `HANDOFF-2026-06-27-lap155.md`. **🧘 Lap-161 DEEP REFLECTION (re-verified in-kernel, 0 math axioms; statement re-audited, no drift):** direction KEPT, directive RE-SYNCED. The lap-155 collapse mandate + the lap-158 generalization both DONE: lap 153 MASTER KEY #1 `genReduct_chain_hasRedex` DROPPED; lap 154 noRedex 6/8; laps 155-157 closed every threadable sub-case; lap 158 SPIKE (`9ac1bf3`) settled the construction = CODE-induction (refuting its own review-half's "outer degree-induction" mandate); **laps 159-160 WIRED + CLOSED the {3,4}-producer cut-reduction core in-kernel** (`repProducerClose` via `certReplace_of_premise_cert` + general IH, consumed at `Crux2Blueprint:3578-3581`). So the deep core of crux-2 (Buchholz Thm 2.1) is CRACKED; the open `residual` (:3451)/`axMajorResidual` (:3735) hold ONLY the STRUCTURAL escape set {(i) ⊥-exit ex-falso → needs internal ⊥-elim/weakening, (ii) C-exit R-intro replay, (iii) tag-5/6 thread-escape (shared)}. Six live sorries, NOT independent: the ex-falso lemma + the anySucc port collapses FOUR (`residual`→noRedex_anySucc→thin-wrap→`axMajorResidual`+`descent_step_K_noncrit_axMajor`); gDef (:4309) separable. VERDICT = genuine narrowing 148→160, but laps 155-160 added 3 anySucc leaves w/o a whole-lemma DROP — next laps must DROP, led by `residual`. MANDATE (DIRECTION.md lap-161) = build the internal ex-falso/weakening lemma FIRST. FORBIDDEN = re-spiking the {3,4} producer / outer degree-induction (DONE + refuted); `red`; `iord`-recursion; `redLeast`; refuted `seqUpdate` splice; axMajor/gDef standalone before the port; M2/M3/M4. ALTITUDE = `false_of_ZDerivesEmpty` sorry-free ≠ headline (`goodstein_implies_consistency` `Reduction.lean:68` bare sorry, NOT YET wired; M2/M4 embedding ~0% built). See `REFLECTION-2026-06-27-lap161.md`, `DIRECTION.md` lap-161. |
| `goodstein_implies_consistency` (Route-A girder, `src/Reduction`) | Rathjen Cor 3.7: `𝗣𝗔⊢γ → 𝗣𝗔⊢Con(𝗣𝗔)` | `sorryAx` only (**lap-89 real** — `PA_delta1Definable` no longer appears; discharged upstream) | 🎯 **THE single open obligation = crux 1 ∘ crux 2.** §3 `γ→PRWO(ε₀)` = **crux 1 — DONE, axiom-clean (lap 57)** via the width-FUNCTION refactor (`BlkRecF`/`StdCor34F`/`crux1_internal_run_F`); in `wip/GentzenCon.lean`. Gentzen Thm 2.8 `PRWO→Con(PA)` = **crux 2, 🟡 ACTIVE FRONTIER**, now localized to the blueprint nut **`redSound`** (`Crux2Blueprint.lean`) = the `red`-reduct of a contradiction derivation is a genuine `ZDerivation` = real internalized cut-elimination; lap 70 forced **Option A** (genuine validity-preserving reduct), lap 82 re-pointed validity to criticality-free `zKValidF`, laps 84–85 DEFINED the genuine reduct `red` (5.1 case). **Lap 86: gating finding (in-kernel, `not_zKCritical_red_zK`) — the critical-only `red` is itself non-critical after one step, so `red`'s tag-4 MUST dispatch Buchholz Def-3.2 cases 5.1/5.2.1/5.2.2** (descent for each banked; new content = dispatch def + 5.2 `zKValidF` validity). Feasibility settled by Bryce–Goré Coq, Feb 2026; must be fully discharged — operator: axiom-free or abandoned. **⭐ Lap-95 FRESH-MIND REVIEW — wall pinned to ONE surgical fix (corrects the lap-92 "ω-rule pivot" framing).** Reading the kernel: **O2 is DONE** (`ZDerivation_zsubst`, `Zsubst.lean:1855`, axiom-clean = benign criticality-free eigensubst; the lap-78 "substitution wall" was the criticality conjunct, dropped when `ZPhi` moved to `zKValidF`) and **O1 is DONE except `ZRegular_red_zK`'s lone false hypothesis `hseltag`** (splice ⟹ `zTag dᵢ = 4`, FALSE under the current `iRK` — splice mis-fires on non-chain selected premises, `not_permIdx_lt_zKseq_zAtom`). The fix is a **surgical gate** on `iRK`'s splice (`zTag dᵢ = 4 ∧ ¬ permIdx dᵢ < lh(zKseq dᵢ)` = critical chain; non-chains → replace 5.2.2), NOT a 2–3k-line ω-rule rewrite — the finitary engine + O1 + O2 are reused; the ω-rule *selection* reading is just the soundness justification. **LANDED IN-KERNEL lap 95 (green 1325, axiom-clean):** `iRK` gated (`iRKDef`/`iRK_defined`/invariants updated), `red_zK_splice` gains `htag`, new `red_zK_rep_nonchain`, and **`ZRegular_red_zK` is now UNCONDITIONAL** (`hseltag` dropped, `[propext, choice, Quot.sound]`). The lap-94 regularity wall is cleared. Residual deep work = the validity half (`red` preserves `ZDerivation` with `tpReduce` conclusion-reduction, lap-90 — `ZDerivation_red_zK` non-chain replace is the new disclosed sorry) + `iord_descent_red`. See `ANALYSIS-2026-06-25-lap95-dispatch-fix-not-pivot.md`. **⭐ Lap-101 DEEP REFLECTION — sub-route fork REOPENED.** Laps 95–100 (Path X) closed the I∀/I¬/axAll non-Rep replace cases but the wall *relocated* to the `redZKReady` "hereditary all-Rep selected spine" motive (`Crux2Blueprint.redSoundGen` K-case `sorry`) — the conclusion-tracking the ω-rule retires for free — and its hard core looks shaky (∅→⊥ chain premises have *growing* antecedents ⟹ Cor 2.1 doesn't reapply down the spine). The lap-92 ω-rule pivot (Path C) was recommended with a de-risk spike *first*; lap-95 committed to Path X **without running it**. CALL: run `wip/InternalZomega.lean` (internal ω-rule ∀-node + substitution-free critical-cut reduct) to settle the fork with evidence; STOP investing in the motive/axNeg until then. Math doubly-proven in the ω-rule presentation (Bryce–Goré Coq + the repo's own axiom-clean meta `Zinfty.lean`). See `REFLECTION-2026-06-25-lap101.md`. |
| `not_proves_of_implies_consistency` / `peano_not_proves_consistency` (Phase 1, `src/Reduction`) | meta-reduction + Gödel II for `𝗣𝗔` | `propext, choice, Quot.sound` (**lap-89 real — axiom-clean**) | 🟢 **CLEAN — the Route-A Gödel-II hook.** ⭐ **Lap 89: `PA_delta1Definable` DISCHARGED UPSTREAM.** Foundation now proves `𝗣𝗔.Δ₁` as a real `noncomputable instance` (`Foundation/FirstOrder/Incompleteness/InductionSchemeDelta1.lean:1379`, no longer an axiom), so `consistent_unprovable 𝗣𝗔` — and hence `peano_not_proves_consistency` and everything chaining through it — carries NO custom axiom. This RETIRES the entire lap-74/78/81 second-front campaign (the `src/PADelta1.lean` Δ₁-recognizer work is now moot/superseded). |
| `InternalThm35.bbeta_*` / `iwtower_cofinal` (internal Thm 3.5, **lap 47**, `src/InternalThm35`) | Rathjen Thm 3.5: slow α → `β` with tight `C(βᵣ)≤r+1` | `propext, choice, Quot.sound` | 🟢 **CLEAN + COMPLETE** — `bbeta_isNF`/`bbeta_C_le`/`bbeta_desc_exists`; ω-tower cofinality `iwtower_cofinal` discharges the seam. Route-independent; consumed by Lemma 3.6 (`nonterminating_internal`). |
| `GentzenCon.prwoInstance_faithful` / `prwoInstance_models_iff` / `eval_prec_internal` (PRWO formulation, **lap 50, REBUILT lap 56**, `wip/GentzenCon`) | Rathjen Thm 2.8: PRWO(ε₀) is the `ℒₒᵣ`-sentence "no ε₀-descent" | `propext, choice, Quot.sound` (**lap-56 real** — SHED the F-φ `native_decide` artifact) | 🟢 **CLEAN** — **lap 56:** rebuilt on the TRANSPARENT `prec_internal`/`InternalONote.icmp` (was the opaque `precφ`=`codeOfREPred₂`, std-model-only spec → wall-B opacity in nonstandard `M`). `prwoInstance_models_iff` (`M⊧prwoInstance seq ↔ ¬∀n y z, seq[y,n]→seq[z,n+1]→icmp z y=0`, every `M⊧IΣ₁`) now holds identically in nonstandard models; `_faithful` is its `M=ℕ` corollary. **natCode↔NF bridge DISSOLVED.** **Crux-2 deep core (lap-58 reframe) = `gentzen_descent_of_inconsistent` (per-model semantic form: `¬𝗣𝗔.Consistent M → infinite ε₀-descent`) — 🟡 ACTIVE FRONTIER** (was 🟠 cited eq-5; reclassified lap 62 — feasibility settled by Bryce–Goré Coq, must be fully discharged). The lap-60/61 `wip/InternalZ.lean` engine (idg/iõ/iord + C3 descent templates, axiom-clean) discharges it once the C0 Fixpoint `ZDerivation`, `iR` (C2), and the **C0.5 Foundation→Z bridge** land. The 9 `GentzenCon` axioms: 5 ℕ-meta scaffold (`ord/R/derivesEmpty/...`, not consumed downstream) + 4 per-model (`gentzen_descent_of_inconsistent`/`gentzenDescentφ`/`_dominated`/`_realized` — the real targets). |
| `peano_not_proves_goodstein_modulo_semantic` / `descentE` / `no_min_descent_absurd_of_goodstein` / `paLX_models_TI_of_PA_provable` (laps 30–44, `src/DescentSemantic`) | the free-X completeness route (Rathjen §3-on-X) | `sorryAx` + native_decide | 🚫 **OFF-PATH (lap 45 obstruction).** The free-X β-wall (`:582`) is the WRONG target — §3-on-X is structurally blocked (`not_dominated_of_diag_le`). Banked, not deleted; `wip/` candidate. NOT wired to `Statement.lean`. |
| `eqLX_subset_paLX` / `eqAxiom_weakerThan_paLX` (lap 32, `src/DescentLift`) | `𝗘𝗤(LX) ⊆ paLX`, hence `𝗘𝗤 ⪯ paLX` | `propext, choice, Quot.sound` | 🟢 clean — every `𝗘𝗤(LX)` axiom is an `lMap Φ`-image of a `𝗣𝗔⁻` axiom or `relExt Xsym`; gives models of `paLX` genuine equality (enables the A2-pt2 `consequence_iff_eq` route). |
| `peano_not_proves_TI` (Thm 5.6, lap 21, **F-φ DISCHARGED lap 28**, `src/Thm56`) | Gentzen 1943: `𝗣𝗔 ⊬ TI_≺(X)` | `propext, choice, Quot.sound, ONoteComp…native_decide.ax_1_5` (lap-30 real) | 🟢 **CLEAN** — full §5 chain C₂→C₁→D→F + D'; F-φ now a theorem (`ONoteComp`). Only 1 🟢 `native_decide` finite artifact. No `sorryAx`, no math axiom. |
| `embed_TI_bounded` (D', **discharged lap 22**, `src/Thm56`) | finite PA-proof ⟹ `Z∞`-proof height `<ε₀` | `propext, choice, Quot.sound, rePred_ltPull_natCode` | 🟢 **CLEAN** — chains `EmbeddingBound.embedC_LX_bdd` (the uniform `∃B<ε₀,∀e,∃α≤B` bound). The lap-21 disclosed `sorry` is gone. |
| `paLX_derivable2_lMap_of_PA_provable` (E-lift, **lap 23**, `src/DescentLift`) | `𝗣𝗔 ⊢ σ ⟹ Derivation2 paLX {lMap σ}` | `propext, choice, Quot.sound` | 🟢 clean — X-free proof translation (`lMap` commutes with `succInd`/`univCl`; schema inclusion `(𝗣𝗔:Schema).lMap Φ ⊆ paLX`). Does NOT reach `TI prec` (X-essential); feeds E-core's X-induction instance. |
| `evalNat_lt_iff`/`evalNat_lt_of_lt` (E-core brick, **lap 23**, `src/DescentCore`) | Rathjen 2.3(iii): `T̂^b_ω` order-reflects on `Canon` | `propext, choice, Quot.sound` | 🟢 clean — `evalNat b o < evalNat b p ↔ o.repr < p.repr` on the `Canon`/`NF` domain, from `canon_repr` + `toOrdinal` strict mono. The workhorse Lemma 3.6 inequality (6) runs on. |
| `peano_not_proves_goodstein_of_descent` (G, **lap 21**, `src/Thm56`) | `DescentE ⟹ 𝗣𝗔 ⊬ γ` | same as Thm 5.6 | 🟢 reduction — pins E's interface (`𝗣𝗔 ⊢ γ → Nonempty (Derivation2 paLX {TI prec})`); headline `sorry` stays until E real |
| `hax_paLX` (C₂ glue, `src/EmbeddingX`) | `paLX`-image axioms embed to `PXFc` | `propext, choice, Quot.sound` | 🟢 **CLEAN (lap 20)** — X-induction assembly discharged via `PXFc_allClosure` + new `rew_succInd`/`rew_subst1_comm_q`/`subst1_comp_bShift` + `metaInduction_cong`. ⟹ `embedC_LX` clean. |
| `goodsteinSentence_faithful` (bridge) | encoding correctness `(ℕ⊧γ) ↔ ∀m∃N goodsteinSeq m N=0` | `propext, choice, Quot.sound` | 🟢 clean (trust base) — **lap 36:** re-proved for the transparent `γ := “∀ m ∃ N, !igoodsteinDef 0 m N”` via `igoodstein_defined.iff`+`igoodstein_nat`; **identical locked RHS**, faithfulness preserved. |
| `goodsteinTerminates_re` (M1) | r.e. of termination | `propext, choice, Quot.sound` | 🟢 clean |
| `Deriv.Provable.cutElim` (M5, §19.9, `src/Zinfty`) | ε₀ cut-elimination (ℒₒᵣ) | `propext, choice, Quot.sound` | 🟢 clean — witness-FREE `(α,c)` |
| `ZinftyGen.…Provable.cutElim` (M5-generic, lap 13) | ε₀ cut-elim over `{L}` | `propext, choice, Quot.sound` | 🟢 clean — the X-route carrier (`L=LX`); reused wholesale, no re-proof |
| `Boundedness.boundedness` (Thm 5.4, **lap 14**) | order-type Boundedness | `propext, choice, Quot.sound` | 🟢 clean — modulo seam hyps `hprec`/`hprecXPos` (discharged at F) |
| `Boundedness.orderType_le_of_TIderiv` (Cor B, **lap 14**) | `Z∞⊢^β_1 TI ⟹ ‖≺‖≤2^β` | `propext, choice, Quot.sound` | 🟢 clean — modulo `hprec`/`hprecXPos`; consumes a cr=0 `XFreeAx` `⊢{TI}` (C₁+C₂ supply it) |
| `embedC` (M4, `src/Embedding`) | PA⊢φ ⟹ Z∞⊢φ (ℒₒᵣ) | `propext, choice, Quot.sound` | 🟢 clean — needs C₂ generic-LX port for the X-route |
| `PXFc.cutElim` (C₁, lap 15, **clean lap 17**, `src/XFreeCutElim`) | `XFreeAx` cut-elim → cr=0 | `propext, choice, Quot.sound` | 🟢 clean — value-congruent literal calculus (`Deriv.axLv`); the lap-16 `atomCut_x` disclosed `sorry` was discharged lap 17 by **`PXFc.nrel_value_subst`** (value-cong negative-literal renaming). |
| `orderType_le_of_TIprovable` (D, **lap 15**) | Thm 5.6 tail `PXFc {TI} ⟹ ‖≺‖≤2^(ω_c^α)` | `propext, choice, Quot.sound` | 🟢 clean — C₁ ∘ corollary B; modulo seam hyps `hprec`/`hprecXPos` (F) |
| `provable_em_x` (C₂, **lap 15**) | `Z∞` excluded middle over LX | `propext, choice, Quot.sound` | 🟢 clean — `XFreeAx`-automatic (never `axTrue`) |
| `metaInduction` (C₂ crux, **lap 15**) | X-induction via cut-tower (Buchholz 5.5) | `propext, choice, Quot.sound` | 🟢 clean — the faithfulness-critical embedding step; abstract in `step` (Foundation-DSL glue ⟹ later) |
| `provable_true_x` (C₂, **lap 16**, `src/EmbeddingX`) | ω-completeness, true closed X-free ⟹ `XFreeAx` | `propext, choice, Quot.sound` | 🟢 clean — the X-free `axm` engine |
| `embedC_LX_gen` (C₂-struct, **lap 16**) | structural embedding `Derivation2 𝓢 Γ ⟹ PXFc` over LX | `propext, choice, Quot.sound` | 🟢 **clean** — all 10 cases (`exs` discharged via `axLv`-based `provable_em_cong_gen_x` + `PXFc.exI_closed`); `axm` abstracted as `hax` |
| `provable_em_cong_gen_x` (C₂, **lap 16**) | value-cong EM over LX (atoms via `axLv`) | `propext, choice, Quot.sound` | 🟢 clean — the `exs` engine, X-atoms safe |
| `hardy_le_of_lt` (M6, `src/Hardy`) | Hardy index monotonicity (Hmono) | `propext, choice, Quot.sound` | 🟢 clean |
| `lowerBound_existential_hardy` (M6) | ∃-fragment 17.1, concrete Hardy/`G` | `propext, choice, Quot.sound` | 🟢 clean — zero abstract hyps |
| `B.allInv` (M6) | ∀-inversion (I∀-frontier resolution) | `propext, choice, Quot.sound` | 🟢 clean |
| `lowerBound_hardy` (M6) | full Thm 17.1 mod `Hdom` | `propext, choice, Quot.sound` | 🟢 clean |
| `lowerBound_hardy_selfcontained` (M6, **lap 6**) | **full Thm 17.1, only `α.NF`** | `propext, choice, Quot.sound` + 12 `native_decide` base-case `ax_*` | 🟢 clean — the `ax_*` are 🟢 finite Goodstein base-case witnesses (acceptable indefinitely) |
| `hardy_add_comp`/`_collapse` (lap 8, `src/Hardy`) | `H_{γ+δ}=H_γ∘H_δ` (non-absorbing) | `propext, choice, Quot.sound` | 🟢 clean — banked Hardy infra (was for the dead Zekd thread; still a usable composition law) |
| `hardy_comp_lt_goodsteinLength` (lap 8, `src/LowerBound`) | `H_α(H_e(m)) < G(m)` eventually | `propext, choice, Quot.sound` + the M6 `native_decide` base-cases | 🟢 clean — banked nested-index domination (reusable if a bridge ever needs a nested control index) |
Math-axiom count (**lap-89 real, build green 1325**): the **headline** is still an honest `sorry`
(`[propext, sorryAx, choice, Quot.sound]`, **0** math axioms). The single open obligation is
`goodstein_implies_consistency` = **crux 1 (DONE, axiom-clean lap 57) ∘ crux 2 (🟡 active frontier — all
three Buchholz case-5 dispatch branches object-complete laps 84–88; remaining = the tag-4 dispatch
assembly + `redSound`)**. ⭐ The former OTHER residual `PA_delta1Definable` is **DISCHARGED UPSTREAM** (lap
89): Foundation proves `𝗣𝗔.Δ₁` as a real instance, so `peano_not_proves_consistency` is axiom-clean and
the endgame is single-front (crux-2 only).
**⚠️ ENDPOINT HARDENED (operator directive, 2026-06-23 — supersedes the lap-53 recommendation):** this
project builds **axiom-free** (trust base `propext, choice, Quot.sound` only) **or is abandoned.** The
headline may **not** rest on a cited `PRWO→Con` (eq-5) axiom — crux 2 must be **fully discharged** — and
`PA_delta1Definable` must **also** be discharged (it is no longer "accept as disclosed"; it is a mandatory
sub-task). The lap-53 "honest best-case = `[propext, choice, Quot.sound, PA_delta1Definable]` with cited
eq-5" is **FORBIDDEN.** This re-classifies **crux 2 from 🟠-generational → 🟡 project-scale frontier debt**,
honest because **feasibility is SETTLED** (the Gentzen `Con(PA)` core was machine-checked in Coq, Feb 2026 —
Bryce–Goré arXiv:2603.00487; ~60% finishable multi-month). Crux 2 lives in `wip/GentzenCon.lean`
(sorry-free, **9 disclosed crux-2 axioms**) + `wip/InternalZ.lean` (0 sorry/0 axiom — the real axiom-clean
implementation). The new C0.5 Foundation→Z bridge (judge Finding 3) is load-bearing; build order =
**Fixpoint `ZDerivation` → `iR` → C0.5 bridge → per-rule C3**. The banked free-X `peano_not_proves_TI`
(0 math axioms) does NOT chain to Con(PA) — keep, don't resurrect (see `HARVEST.md`).

## Pointers
ROADMAP/plan: `EXPEDITION-PLAN.md`, `PHASE2-DECOMPOSITION.md` · **route resolution (lap 46): memory
`route-resolved-prwo-gentzen` + `Reduction.lean` docstring** · architecture review: `E-ARCHITECTURE-REVIEW
-2026-06-23.md` + `E-ARCHITECTURE-RESPONSE-2026-06-23.md` · lap-44 reflection: `REFLECTION-2026-06-23-lap44.md`
· newest baton: `HANDOFF-2026-06-27-lap160.md` (find via `ls HANDOFF-*-lap*.md | sort -t p -k2 -n | tail -1`)
· latest reflection: `REFLECTION-2026-06-27-lap161.md` · open-items: `PENDING_WORK.md` · charter: `DIRECTION.md` (CURRENT DIRECTIVE lap-161)
(CURRENT DIRECTIVE = lap-152) · outside-judge baton: `JUDGE-HANDOFF-2026-06-26-lap150.md`
