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

**lap-164 (FRESH-MIND REVIEW) — KEEP. Direction unchanged from lap-161 (existence-form pivot; finish
`false_of_ZDerivesEmpty` = M1b-term). Lap-163 DISCHARGED escape (i) ⊥-exit ex-falso in-kernel (`zAxBot`
tag-8 + `exFalsoClose`, axiom-clean — exactly what the lap-161 mandate ordered). Re-verified (real
`#print axioms`, build 🟢 1326): headline `peano_not_proves_goodstein` + `false_of_ZDerivesEmpty` =
`[propext, sorryAx, choice, Quot.sound]` (0 math axioms); `peano_not_proves_consistency` +
`goodsteinSentence_faithful` clean. Six live sorries (re-synced line #s): `ind_reduct_anySucc` :3410,
`genReduct_chain_hasRedex_anySucc` :3424, `residual` :3475, `axMajorResidual` :3787,
`descent_step_K_noncrit_axMajor` :4253, gDef :4378.**
**→ NEXT MOVE (binding): close the remaining `residual` (:3475) — the only two families left are (ii)
C-exit R-intro replay (tag-1/2 major producing the conclusion succedent `C`; dispatch lands at :3613/:3619)
and (iii) tag-5/6 thread-escape (:3631/:3646 + the `tryProducerClose`/`closeZAxNeg` residual landings).
FIRST decompose `residual` into ONE named src sub-`sorry` per family (`cExitReplay` / `threadEscapeClose`)
— that itself counts as a DROP-shaped advance — then close (ii) via the major premise's OWN R-intro reduct
spliced same-end-sequent (it is already a `zIall`/`zIneg` deriving `Γⱼ→C`; weaken/rebase to `Γ→C`,
`õ`-drops as a strict sub-derivation), and (iii) via a shared `threadEscapeClose` reused by `axMajorResidual`.
Closing `residual` cascades: drops `genReduct_chain_noRedex_anySucc` → thin-wraps `genReduct_anySucc` →
drops `axMajorResidual` + `descent_step_K_noncrit_axMajor`. gDef (:4378) is the separable fifth. ALTITUDE
CAUTION (unchanged, binding): a sorry-free `false_of_ZDerivesEmpty` is NOT the headline —
`goodstein_implies_consistency` (`Reduction.lean:68`) is a bare sorry, NOT YET wired (M2/M4 ~0%); the lap
that closes `false_of_ZDerivesEmpty` HANDS to an altitude lap to re-plan M2. Everything else (FORBIDDEN list,
forbidden engines) per the lap-161 block below — unchanged.**

**Set: lap-161 (DEEP REFLECTION, every-9th; prev altitude lap-158). Supersedes lap-158. Direction KEPT
(existence-form / constructive-`GenReductCert` pivot off `red`; finish `false_of_ZDerivesEmpty` = M1b-term).
RE-SYNCED to reality: the lap-158 directive is STALE. It mandated a "degree-induction design spike FIRST"
that the lap-158 spike ITSELF already ran AND refuted (`9ac1bf3`: the {3,4} producer closes by the existing
CODE-induction with LOCAL per-flatten degree headroom from the premise's own `irk+1 ≤ idg(premise)` — NO outer
degree-induction). Laps 159-160 then WIRED and CLOSED that {3,4}-producer core in-kernel (`repProducerClose`
via `certReplace_of_premise_cert` + the general IH; build 🟢; consumed in the live dispatch at
`Crux2Blueprint:3578-3581`). So "the irreducible heart of crux-2" the old directive names as open is CRACKED.
Re-verified (lap 161, real `#print axioms`, build 🟢 1326): headline `peano_not_proves_goodstein` =
`[propext, sorryAx, choice, Quot.sound]` (0 math axioms, bare-sorry headline); `peano_not_proves_consistency`
+ `goodsteinSentence_faithful` = `[propext, choice, Quot.sound]` (clean); `false_of_ZDerivesEmpty` =
`[propext, sorryAx, choice, Quot.sound]` (0 math axioms) — no drift.**

- **THE objective (only this):** drive `false_of_ZDerivesEmpty` (`Crux2Blueprint:4394`) to **0 sorries**.
  The {3,4}-producer cut-reduction (the genuine feasibility risk) is DONE; what is left is STRUCTURAL +
  one definability bound. The six live sorries: `ind_reduct_anySucc` (:3382), `genReduct_chain_hasRedex_anySucc`
  (:3391), `genReduct_chain_noRedex_anySucc`/`residual` (:3407/:3451), `genReduct_chain_noRedex`/`axMajorResidual`
  (:3683/:3735), `descent_step_K_noncrit_axMajor` (:4180, the Γ=∅ twin), gDef (:4309).
- **THE residual is NO LONGER the {3,4} producer — it is the STRUCTURAL escape set.** `residual` (:3451) and
  `axMajorResidual` (:3735) are now reached ONLY for: (i) **⊥-exit ex-falso** — a tag-0/7 leaf or tag-5 escape
  puts `⊥∈Γ` (or `^∀⊥∈Γ`), and `⊥∈Γ ⟹ Γ→C` has NO single Z-rule (the lone ex-falso `zAxNeg` needs a
  complementary `¬q,q` pair, not bare `⊥`); (ii) **C-exit R-intro replay** — a tag-1/2 major produces the
  conclusion succedent `C` directly; (iii) the **tag-5 climb-escape** (`^∀G∈Γ`) + **tag-6 partial thread**
  (shared between `residual` and `axMajorResidual` — prove ONCE). (i) is the one genuinely-new piece (lap-160
  finding #2: needs an internal **⊥-elim / weakening** lemma); (ii)/(iii) are reuse/threading.
- **MANDATED move — build the internal EX-FALSO / WEAKENING lemma FIRST, then wire it to close `residual`.**
  As a STANDALONE reusable Z-lemma: `⊥ ∈ seqAnt s ⟹ ∃ d', ZDerivation d' deriving (s's antecedent)→C` with a
  finite-head ordinal that `õ`-drops vs `zK s r ds` (mirror `leafCloseC`/`axNegCloseGen` at :3462/:3473 — same
  cert shape), plus the `^∀⊥∈Γ` variant for the tag-5 escape. Then discharge `residual` (:3451) case-by-case:
  (i) → the new ex-falso lemma; (ii) → the major premise's own reduct, spliced same-end-sequent; (iii) → the
  shared thread (factor a `threadEscapeClose` reused by `axMajorResidual`). Closing `residual` DROPS the
  `genReduct_chain_noRedex_anySucc` leaf; finishing the other two anySucc leaves makes `genReduct_botSucc`
  (and `genReduct_anySucc`) a thin wrapper that DROPS `axMajorResidual` (:3735) AND its Γ=∅ twin
  `descent_step_K_noncrit_axMajor` (:4180, same content). One structural lemma + the port collapses FOUR of
  the six live sorries. gDef (:4309) is the separable fifth piece (below).
- **gDef (`exists_sigma1_descending_step` :4309)** — the Σ₁-definable step function. NOT μ-min (wrong polarity,
  refuted lap-139). Route: a primrec WITNESS BOUND `∃ d' ≤ B(w)` on the reduct CODE (then bounded-`μ` is Δ₁,
  see `wip/WitnessBound.lean`), OR make the now-constructive `genReduct` reduct a definable function so `g` is
  deterministic. Attack only AFTER the cut-elimination residuals close (the constructive reduct is the input).
- **Success metric:** a WHOLE-LEMMA `src` sorry DROPS (not just an internal residual narrowed). Laps 155-160
  closed sub-cases but the whole-lemma count went 4→6 (3 anySucc leaves added); the next laps must DROP, led by
  `residual` (:3451). Decomposing `residual` into named src sub-`sorry`s (one per escape case) also counts.
- **FORBIDDEN:** re-attacking / re-spiking the {3,4}-producer core or "outer degree-induction" (DONE + the
  degree-induction hypothesis REFUTED by its own lap-158 spike — do not rebuild it); witnessing any branch with
  `red`; `iord`-recursion for the construction (CODE-induction + local-degree flatten ONLY); `redLeast`/μ-min
  for gDef (refuted lap-139); the refuted single-premise `seqUpdate` splice (`descent_step_K_splice`, lap-151);
  attacking `descent_step_K_noncrit_axMajor` :4180 or gDef :4309 STANDALONE *before* the anySucc port wires them
  (they collapse FROM the port, not in isolation); the off-path dead `red`-soundness sorries
  {:82,:1257,:1367,:1563,:1653,:1765,:1868} AS STATED; **M2 / M3 / M4 wiring** (the embedding bridge +
  `goodstein_implies_consistency`) — still off-limits until `false_of_ZDerivesEmpty` is sorry-free.
- **Why:** the {3,4}-producer cut-reduction was the one piece of crux-2 whose feasibility was in doubt, and it
  CLOSED at laps 158-160 — major de-risking. The remainder of `false_of_ZDerivesEmpty` is admissible-rule
  structural work (ex-falso/weakening, R-intro replay, threading) + a primrec code bound — laborious but not
  feasibility-threatening, a handful of laps from a clean, citable milestone. Finishing it is the right thing
  to do before pivoting to the unbuilt bridge. **ALTITUDE CAUTION (sharpened, binding):** a sorry-free
  `false_of_ZDerivesEmpty` is NOT the headline. `goodstein_implies_consistency` (`Reduction.lean:68`) is a BARE
  sorry; `false_of_ZDerivesEmpty` is NOT YET WIRED to it (the M2/M4 embedding — PA-proof → `ZDerivesEmptyR` — is
  ~0% built); girder #1 (γ→PRWO, internal Cor 3.4) is only partly built. "0 math axioms / only the crux left"
  must NOT read as "almost done." The lap that closes `false_of_ZDerivesEmpty` should hand to an altitude lap to
  RE-PLAN toward the M2 bridge — that becomes the dominant feasibility unknown.

### Directive history (newest first; append one line per altitude lap — never delete)
- **lap-164** (FRESH-MIND REVIEW): direction KEPT (lap-161 still current; the operator's "M1b-term only / existence-form spike first" kickoff is SATISFIED — the spike was adopted laps 132/138 and M1b-term = `false_of_ZDerivesEmpty`, the lemma being driven). Lap-163 executed the lap-161 mandate: escape (i) ⊥-exit ex-falso CLOSED via `zAxBot` (tag-8) + `exFalsoClose`, axiom-clean (no sorryAx in `zDerivation_zAxBot`). Re-verified (real `#print axioms`, build 🟢 1326): headline + `false_of_ZDerivesEmpty` 0 math axioms; consistency/faithful clean; no drift. CRUX-NEGLECT CHECK: laps 161-163 all hit the directive's named piece (ex-falso), not side-leaves — not fixation; but `false_of_ZDerivesEmpty` is the cut-elim ENGINE, still UNWIRED to the headline's bare sorry (`goodstein_implies_consistency`, M2/M4 ~0%) — the dominant feasibility unknown remains M2, deferred by design until the engine closes. NEXT MOVE = close the remaining `residual` (:3475): only (ii) C-exit R-intro replay (tag-1/2) + (iii) tag-5/6 thread-escape left; FIRST decompose into named src sub-`sorry`s (`cExitReplay`/`threadEscapeClose`), then close (ii) via the major premise's own R-intro reduct spliced same-end-sequent, (iii) via a shared `threadEscapeClose` reused by `axMajorResidual`. Closing `residual` cascades to drop `genReduct_chain_noRedex_anySucc` → `axMajorResidual` → `descent_step_K_noncrit_axMajor`. FORBIDDEN/engines per lap-161. ALTITUDE CAUTION (binding): the lap that closes `false_of_ZDerivesEmpty` hands to an altitude lap to re-plan the M2 bridge — "only the crux left" ≠ "almost done."
- **lap-161** (DEEP REFLECTION, every-9th): direction KEPT (existence-form / constructive-`GenReductCert` pivot; finish `false_of_ZDerivesEmpty` = M1b-term). RE-SYNCED the stale lap-158 directive. FINDING = lap-158 was internally contradictory: its review half mandated an "outer degree-induction design spike FIRST," but its OWN spike (`9ac1bf3`) refuted that hypothesis — the {3,4} producer closes by the EXISTING code-induction with LOCAL per-flatten degree headroom (premise's own `irk+1 ≤ idg(premise)`), no global degree-induction. Laps 159-160 then WIRED + CLOSED that {3,4}-producer core in-kernel (`repProducerClose` via `certReplace_of_premise_cert` + general IH; build 🟢; consumed at `Crux2Blueprint:3578-3581`). So the "irreducible heart of crux-2" is CRACKED; the open `residual` (:3451)/`axMajorResidual` (:3735) now hold ONLY the STRUCTURAL escape set — (i) ⊥-exit ex-falso (`⊥∈Γ ⟹ Γ→C`, needs internal ⊥-elim/weakening — the one new piece), (ii) C-exit R-intro replay, (iii) tag-5/6 thread-escape (shared). Re-verified axiom-clean (real `#print axioms`, build 🟢 1326): headline 0 math axioms (bare sorry), consistency/faithful clean, `false_of_ZDerivesEmpty` 0 math axioms, no drift. VERDICT = progress GENUINE (steady crux narrowing 153→160; the {3,4} core actually closed), but laps 155-160 added 3 anySucc leaves WITHOUT dropping a whole-lemma src sorry — next laps must DROP. MANDATE = build the internal EX-FALSO/WEAKENING lemma FIRST (standalone, mirror `leafCloseC`/`axNegCloseGen` cert shape), wire it + R-intro replay + shared thread to CLOSE `residual` (:3451) → drops the noRedex_anySucc leaf → (with the 2 other anySucc leaves) thin-wraps `genReduct_botSucc` → DROPS `axMajorResidual` + `descent_step_K_noncrit_axMajor`; gDef (:4309) separable (witness-bound/constructive reduct, NOT μ-min). FORBIDDEN = re-spiking the {3,4} producer / outer degree-induction (DONE + refuted); `red`; `iord`-recursion; `redLeast`; the refuted `seqUpdate` splice; axMajor/gDef standalone before the port; off-path dead red-soundness sorries; M2/M3/M4 wiring. ALTITUDE CAUTION (sharpened) = `false_of_ZDerivesEmpty` sorry-free is NOT the headline — `goodstein_implies_consistency` (`Reduction.lean:68`) is a bare sorry, NOT YET wired to `false_of_ZDerivesEmpty`; the M2/M4 embedding bridge is ~0% built; "only the crux left" ≠ "almost done." The lap that closes `false_of_ZDerivesEmpty` hands to an altitude lap to re-plan the M2 bridge.
- **lap-158** (FRESH-MIND REVIEW): direction KEPT (existence-form pivot off `red` + `genReduct_botSucc` code-recursion). lap-155's SUCCEDENT-THREADING COLLAPSE mandate is DONE + EXHAUSTED — lap 155 tag-5(a)+ordinal lemmas, lap 156 tag-6(a)+zAxNeg producer+`leastSucc_in_ant_or_nonleaf`, lap 157 `climb_to_rep_producer` (axiom-clean) → tag-5 zAxAll producer collapses. Every threadable/closeable sub-case of `axMajorResidual` (`Crux2Blueprint:3417`) is closed; the lap-155 collapse-to-exhaustion GATE IS MET. Re-verified axiom-clean (real `#print axioms`): headline `[propext,sorryAx,choice,Quot.sound]` 0 math axioms; consistency/faithful clean; `false_of_ZDerivesEmpty` 0 math axioms; no drift; build 🟢 1326. VERDICT = progress GENUINE (steady crux narrowing 153→157, not fixation/leaf-neglect). FINDING = the residual is now the IRREDUCIBLE {3,4}-producer cut-reduction = Buchholz Thm 2.1 general cut-elimination (the heart of crux-2), NOW UN-FORBIDDEN (gate met): a NON-LEAF `Rep` producer that genuinely PRODUCES the cut formula — un-threadable (laps 155-157) AND un-reducible by same-degree õ-drop (REFUTED in-kernel lap 157; `irk(cut)+1≤idg` not derivable). Shapes: (i) tag-5+climb → `^∀^k⊥` (∀-tower over CLOSED ⊥, dominant); (ii) tag-6 → arbitrary `p'`. MANDATE = DESIGN SPIKE FIRST (wip/, lap-101/132-style) pinning the generalized statement: OUTER induction on DEGREE `idg` (a NAT — kosher) + INNER code-induction, eliminate highest-rank cuts first (= the missing headroom), reuse the `genReduct_chain_hasRedex` degree-drop engine + same-end-sequent `certReplace`; EXPLORE the cheap `^∀⊥→⊥` vacuous-instantiation inversion for shape (i) but confirm it beats the degree-general route (needs change-of-succedent splice) before committing; THEN port to src as named sub-`sorry`s. FORBIDDEN = blind src refactor before the spike pins the statement; same-degree õ-drop for the {3,4} producer (refuted lap 157); `red`; `iord`-recursion (degree-induction on NAT `idg` + CODE only); `redLeast`; the refuted `seqUpdate` splice; axMajor/gDef standalone; off-path dead red-soundness sorries; M2/M4. ALTITUDE CAUTION = M2 (Foundation→Z bridge) ~0% built — "only the crux left" ≠ "almost done."
- **lap-155** (FRESH-MIND REVIEW): direction KEPT (existence-form pivot off `red` + `genReduct_botSucc` code-recursion). lap-152's mandate DONE — `genReduct_chain_hasRedex` DROPPED (lap 153) + `genReduct_chain_noRedex` 6/8 branches PROVEN (lap 154). Re-verified axiom-clean (headline `[propext,sorryAx,choice,Quot.sound]` 0 math axioms; faithful/consistency clean; statement no drift). The whole termination crux = the ONE open leaf `axMajorClose` (tag-5/6 L-axiom cut-partner, `Crux2Blueprint:3418`). **COURSE-CORRECTION:** the lap-154 handoff frames its sub-case (b) as the lap-136 general-succedent reduction (the repo's hardest target, kernel-refuted at face value); the review judges that PESSIMISTIC + PREMATURE. Kernel-grounded insight: cut formula is `^∀⊥` (`p=⊥`); under `hnolow` a direct R-intro `zIall` of `^∀⊥` below j0 is IMPOSSIBLE (would `isRedexPair` with jstar — VERIFIED `isRedexPair:4820` fires on `(zIall ^∀p, zAxAll ^∀p)`), so `^∀⊥` is never CREATED, only threaded from Γ. MANDATE = the SUCCEDENT-THREADING COLLAPSE (sub-case (a) `^∀⊥∈Γ` via 2 reusable ordinal lemmas `w<ω^w`+summand-≤-fold + generalize `majorPrem_*_cutPartner` off `seqAnt s=∅`; collapse sub-case (b): leaf→`chainAsucc_threaded_of_leaf`, R-intro→`hnolow`, zK→recurse, residual at most a `zInd` concluding `^∀⊥` — check it's even derivable). FORBIDDEN = building the lap-136 reduct BEFORE the collapse is tested to exhaustion; `red`; `iord`-recursion; `redLeast`; the refuted `seqUpdate` splice; axMajor/gDef standalone. ALTITUDE CAUTION = M2 (Foundation→Z bridge) ~0% built — "only the crux left" ≠ "almost done."
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
