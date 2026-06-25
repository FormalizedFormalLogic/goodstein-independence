# STATUS — GoodsteinPA 📊

**Kirby–Paris: `𝗣𝗔 ⊬ Goodstein`. ROUTE RESOLVED (lap 45→46) to Rathjen 2014 Cor 3.7 = the original
DIRECTION/Gödel-II plan: `𝗣𝗔⊢γ →(§3, all primrec) 𝗣𝗔⊢PRWO(ε₀) →(Gentzen Thm 2.8(i)) 𝗣𝗔⊢Con(𝗣𝗔)`, then
Gödel II.** The §3 internal pipeline = internal Cor 3.4 (Grzegorczyk `g`-padding, internal level — DEEP,
open) → internal Thm 3.5 (slow α → tight `C(βᵣ)≤r+1` — **COMPLETE lap 47**, `InternalThm35`) → Lemma 3.6
(`nonterminating_internal`, done). The Buchholz free-X `peano_not_proves_TI` (axiom-clean) is a **banked
asset, OFF the headline path** (free-X-TI ⊢ PRWO, wrong direction). **Crux 1 (`γ→PRWO`) LANDED axiom-clean
(lap 57); crux 2 (`PRWO→Con`, Buchholz-Z ordinal analysis arithmetized in IΣ₁) is the sole remaining math
content — the 🟡 active frontier, now sharply localized to `RedSound` (InternalZ.lean): the `iR2`-reduct of
a contradiction derivation must itself be a genuine `ZDerivation` = real internalized cut-elimination.** ·
**Build**: 🟢 green (`lake build GoodsteinPA`, 1325 jobs) · **Updated**: lap 95 (FRESH-MIND REVIEW —
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
> have). **This lap landed** `wip/InternalZdispatch.lean` (axiom-clean de-risk spike): gated `iRKfix` +
> invariants + **`ZRegular_iRKfix`** closing `hseltag` from the gate. **NEXT:** port the gate in-place into
> `iRK` (+ `red_zK_rep`/`red_zK_splice`/`ZRegular_red_zK`/`Crux2Blueprint`), green build; then the deep
> validity half (`tpReduce` conclusion-reduction) + `iord_descent_red` + wire to headline.

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
**(lap-95 FRESH-MIND REVIEW — CURRENT read.)** Build green **1325**; headline honest `sorry` (real `#print
axioms = [propext, sorryAx, Classical.choice, Quot.sound]`, 0 math axioms; `peano_not_proves_consistency`
clean). Single open obligation = `goodstein_implies_consistency` = crux-1 (DONE) ∘ **crux-2** = `redSound`.
**The crux-2 wall is now pinned to ONE surgical fix.** O2 (eigenvariable substitution) is DONE
(`ZDerivation_zsubst`, axiom-clean — the lap-78 "substitution wall" was the criticality conjunct, dropped
when `ZPhi` moved to `zKValidF`). O1 (`ZRegular` freshness) is DONE except `ZRegular_red_zK`'s lone
hypothesis `hseltag` (splice ⟹ `zTag dᵢ = 4`), which is FALSE under the current `iRK` (the splice mis-fires
on non-chain selected premises). **Fix = gate `iRK`'s splice on `zTag dᵢ = 4 ∧ ¬ permIdx dᵢ < lh(zKseq dᵢ)`
(critical chain); route non-chains to the replace (Buchholz 5.2.2).** This is NOT the lap-92 "2–3k-line
ω-rule pivot" — the finitary engine + O1 + O2 are all reused; the ω-rule *selection* reading is just the
soundness justification. De-risked this lap in `wip/InternalZdispatch.lean` (gated `iRKfix` + `ZRegular_iRKfix`,
axiom-clean). NEXT: port the gate in-place (green build), then the deep validity half (`tpReduce`
conclusion-reduction) + `iord_descent_red` + wire to headline. See
`ANALYSIS-2026-06-25-lap95-dispatch-fix-not-pivot.md`, `PENDING_WORK.md` lap-95 box.

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
- **2026-06-25 (lap 95 — FRESH-MIND REVIEW):** Re-verified kernel (real `#print axioms`, green 1325): headline
  `[propext, sorryAx, choice, Quot.sound]` (0 math axioms), `peano_not_proves_consistency` clean. **Direction
  KEPT, Path X CONFIRMED + SHARPENED.** Dissolved the lap-92 "Path X vs ω-rule pivot / 2–3k-line rewrite"
  fork by reading the kernel: **O2 DONE** (`ZDerivation_zsubst` axiom-clean) and **O1 DONE except one leaf**
  (`ZRegular_red_zK` proved modulo the lone hypothesis `hseltag`). The entire remaining regularity wall = that
  ONE false hypothesis (`hseltag`: splice ⟹ `zTag dᵢ = 4`, FALSE under the current `iRK` splice dispatch).
  Fix = a SURGICAL gate (splice only when dᵢ is a critical chain); the ω-rule *selection* reading is just the
  soundness justification, not a rebuild. Landed `wip/InternalZdispatch.lean` (axiom-clean de-risk spike):
  gated `iRKfix` + invariants + `ZRegular_iRKfix` (closes `hseltag` from the gate). Wrote
  `ANALYSIS-2026-06-25-lap95-dispatch-fix-not-pivot.md`; refreshed STATUS + PENDING_WORK. NEXT = port the gate
  in-place into `iRK` (green build), then the deep validity half (`tpReduce`) + `iord_descent_red` + headline.
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

### Short-term (mirror PENDING_WORK top) — crux 2 = `redSound`, the SURGICAL dispatch gate, hardest-first
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
`[propext, choice, Quot.sound]`. The endgame is therefore single-front: discharge crux-2 and the headline
closes axiom-clean with no remaining upstream-axiom reconciliation.

## Axiom ledger (per headline / landmark theorem — the fidelity spine)
| theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `peano_not_proves_goodstein` (headline, `Statement.lean`) | uncond. (Kirby–Paris) | `propext, sorryAx, choice, Quot.sound` (**lap-95 real, re-verified in-kernel**) | 🔓 open `sorry` (LOCKED, anti-fraud) — **0** math axioms; `sorryAx` traces the lone math `sorry` `goodstein_implies_consistency` = crux-2 = `redSound`. Route A: reduces (axiom-clean) to `goodstein_implies_consistency` via `not_proves_of_implies_consistency` + Gödel II. |
| `goodstein_implies_consistency` (Route-A girder, `src/Reduction`) | Rathjen Cor 3.7: `𝗣𝗔⊢γ → 𝗣𝗔⊢Con(𝗣𝗔)` | `sorryAx` only (**lap-89 real** — `PA_delta1Definable` no longer appears; discharged upstream) | 🎯 **THE single open obligation = crux 1 ∘ crux 2.** §3 `γ→PRWO(ε₀)` = **crux 1 — DONE, axiom-clean (lap 57)** via the width-FUNCTION refactor (`BlkRecF`/`StdCor34F`/`crux1_internal_run_F`); in `wip/GentzenCon.lean`. Gentzen Thm 2.8 `PRWO→Con(PA)` = **crux 2, 🟡 ACTIVE FRONTIER**, now localized to the blueprint nut **`redSound`** (`Crux2Blueprint.lean`) = the `red`-reduct of a contradiction derivation is a genuine `ZDerivation` = real internalized cut-elimination; lap 70 forced **Option A** (genuine validity-preserving reduct), lap 82 re-pointed validity to criticality-free `zKValidF`, laps 84–85 DEFINED the genuine reduct `red` (5.1 case). **Lap 86: gating finding (in-kernel, `not_zKCritical_red_zK`) — the critical-only `red` is itself non-critical after one step, so `red`'s tag-4 MUST dispatch Buchholz Def-3.2 cases 5.1/5.2.1/5.2.2** (descent for each banked; new content = dispatch def + 5.2 `zKValidF` validity). Feasibility settled by Bryce–Goré Coq, Feb 2026; must be fully discharged — operator: axiom-free or abandoned. **⭐ Lap-95 FRESH-MIND REVIEW — wall pinned to ONE surgical fix (corrects the lap-92 "ω-rule pivot" framing).** Reading the kernel: **O2 is DONE** (`ZDerivation_zsubst`, `Zsubst.lean:1855`, axiom-clean = benign criticality-free eigensubst; the lap-78 "substitution wall" was the criticality conjunct, dropped when `ZPhi` moved to `zKValidF`) and **O1 is DONE except `ZRegular_red_zK`'s lone false hypothesis `hseltag`** (splice ⟹ `zTag dᵢ = 4`, FALSE under the current `iRK` — splice mis-fires on non-chain selected premises, `not_permIdx_lt_zKseq_zAtom`). The fix is a **surgical gate** on `iRK`'s splice (`zTag dᵢ = 4 ∧ ¬ permIdx dᵢ < lh(zKseq dᵢ)` = critical chain; non-chains → replace 5.2.2), NOT a 2–3k-line ω-rule rewrite — the finitary engine + O1 + O2 are reused; the ω-rule *selection* reading is just the soundness justification. De-risked lap 95 in `wip/InternalZdispatch.lean` (gated `iRKfix` + `ZRegular_iRKfix`, axiom-clean). Residual deep work after the gate = the validity half (`red` preserves `ZDerivation` with `tpReduce` conclusion-reduction, lap-90) + `iord_descent_red`. See `ANALYSIS-2026-06-25-lap95-dispatch-fix-not-pivot.md`. |
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
· newest baton: `HANDOFF.md` → newest dated HANDOFF · open-items: `PENDING_WORK.md` · charter: `DIRECTION.md`
