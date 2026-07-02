# E — JUDGE validation of REBUILD-Z laps 8–9 (Ren, 2026-07-02)

> Judge pass over lap 8 (global 187, the src port + ladder erection per
> `REBUILD-Z-LAP8-ENTRANCE-2026-07-02.md`) and lap 9 (global 188, the self-directed crux
> sharpening). Baseline for the freeze: **`6d0c6b6`**. Provenance: BOTH laps ran as external
> codex sessions (no c-yolo preamble); unlike lap 7 they committed their own artifacts
> (`51bec9f..ec0063a`, `0cdc2f9`/`b41fd87`). Every gate below was re-run by this judge from the
> kernel up; the codex narrative was trusted for nothing.

## 1. Verdict

- **Port (P-a/b/c/e/f): PASS — ratified.** Verbatim vs the wip freeze references; `toZef`
  mandate followed exactly; read-offs discharged by reuse; P-f's docstring annotation was the
  one skipped item (completed by the judge with this ruling).
- **P-d: PARTIAL as ordered — `allInv_Zef2` discharged (real), ewN bank real, pins 1–2
  correctly escalated.** The escalation is RATIFIED and now RESOLVED: see ruling #1 (§3) —
  **trap 9**, the ninth statement trap, caught at statement/probe time.
- **Ladder (L-items): PARTIAL — L-R ratified; L-D and L-W VOID (trap 10, judge-caught);
  L-E's escalation honored but its placeholder statement is VOID** (§4).
- **Lap 9: PASS — the sharpening is ratified**, both probes independently re-verified in the
  kernel by this judge. Its "binary" framing is corrected by ruling #1: the resolution is a
  third form the binary missed — the paper's own.
- **Decision #3 (ladder representation): CONFIRMED** — verified in `src/BlueprintAudit.lean`
  itself: `categoryOfFootprint` returns `.broken` on any `sorryAx` footprint and `reconcile`
  FAILs `broken` unconditionally, so sorry pins cannot carry `@[goodstein_blueprint]` rows
  without an axiom (FORBIDDEN). The tex dep-graph is the faithful representation. Ratified.

## 2. Independent re-verification (all run by this judge)

- **Freeze**: `git diff 6d0c6b6..HEAD -- src/GoodsteinPA/OperatorZeh.lean` EMPTY (stricter than
  the docstring-only allowance); wip reference files (`wip/EwIter.lean`, `wip/Zef2Calculus.lean`)
  byte-identical to `6d0c6b6`.
- **Port fidelity**: decl-by-decl comparison of `OperatorZef2.lean` against `wip/Zef2Calculus.lean`
  — `Zef2` inductive, `mono_f`/`change_H`/`mono_Hf`, `Zef2Prov` (+`of`/`weakening`), the read-off
  signatures, `cutElimPass_Zef2`, `ewRootSlot`(+f1/f2 with identical proofs), C3 exit: VERBATIM.
  Additions (gate projection, `toZef`, `Zef2Prov.mono`/`toZefProv`, ewN bank, pins, rungs) all
  order-sanctioned. `EwIter.lean` carries the wip statements verbatim; P2/P3 probes correctly
  left in wip (src anchor-free).
- **Pins 1–2 statement fidelity**: `cutReduceAllAuxRunning_Zf2` / `stepAllω_Zf2` are EXACT
  mechanical `Zef→Zef2` ports of `OperatorZeh.lean:1523`/`:1752` — every hypothesis
  (`hg_mono`/`hg_infl`/`Monotone f`/inflationarity) was already in the Zef originals; nothing
  smuggled.
- **Gates**: build 🟢 1341 (own run) · headline `peano_not_proves_goodstein` =
  `[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]` UNDRIFTED (own
  scratch) · `lean-sorry src/` delta vs baseline = EXACTLY the 7 disclosed pins in
  `OperatorZef2.lean` (old pin 3 unchanged; Crux2/DescentSemantic banks unchanged) · NO new
  `axiom` · NO `native_decide` in the ported files · `blueprint_audit` PASSED 16/16 (own run).
- **Axiom sweep** (own scratch): `toZef`, `gate`, `toZefProv`, `readoff_sigma1_Zef2`,
  `headline_readoff_Zef2`, `allInv_Zef2`, `ewN_addAux_le`/`ewN_add_le`/`ewN_osucc_le`/
  `ewN_osucc_add_le`, `collapseIter_NF`, `ewRootSlot_f1`/`_f2`, EwIter spine (P1 lift,
  `ewIter_rel1_le`, `mem_ewBall_of_ewN_le`) — ALL standard triple (or leaner). The 7 pins +
  `cutElimPass_exit_root_Zef2` are sorryAx-bearing, the exit's sorryAx flowing only through the
  pass pin.
- **Lap-9 probes** (own compile + sweep): `noOsucc_closes` = `[propext, Quot.sound]`;
  `osucc_plus_one_refutes` = standard triple; `fBad_EwF1`/`gBad_EwF1` real — checked against
  `EwF1`'s actual definition (`StrictMono ∧ 2m+1 ≤ f m`): both slots genuinely qualify, the
  refutation is honest.

## 3. RULING #1 — the reduction gate trap (trap 9): resolved PAPER-LITERAL, not (a) or (b)

Ground truth re-read from the E–W PDF (pp. 8–12), which neither lap consulted:

1. **Def 23's judgment side condition is the FIXED-BASE gate**: `f, F ⊢^α_ρ Γ` requires
   `max{N(F(0)), N(α)} ≤ f(0)` (HYP(f;F;α)). `Zef2`'s `hαN : ewN α ≤ f 0` is Def-23-faithful
   as it stands. **Fix (b) is REFUSED**: the `K = f(ewN α + m)` form the lap-9 handoff called
   "the genuine E–W design" is **Def 16** — the ITERATE's gate — not the judgment's. (b) would
   deviate FROM the paper, and it would invalidate the whole ported layer + read-off for nothing.
2. **Lemma 25 (Cut-reduction) concludes at `α + β` — there is NO successor bump in the paper.**
   The repo's `osucc (α + γ)` was a self-inflicted cascade: bump the pin's conclusion once and
   the IH returns a bumped witness (`osucc (α+βφ) = α+γ`), forcing the next bump. The paper's
   induction never bumps: the principal case lands premises at `α + β₀ < α + β` (strict by
   right-addition) and the inverted side at `α < α + β` (`β > 0` in the principal case). The
   lap-9 analysis's "the +1 is intrinsic" holds only GIVEN the bumped statement — restating the
   conclusion is exactly the architect-owned move the escalation asked for.
3. **The box already proved the fix works**: `noOsucc_closes` IS the kernel proof that the
   `α + γ` root's gate closes — `ewN (α+γ) ≤ ewN α + ewN γ` (sub-additivity, banked
   `ewN_add_le`; **exact additivity was never needed** — the gate is an upper bound) and
   `g 0 + f 0 ≤ g (f 0)` (`strictMono_base_add_le`). Fix (a)'s natural-sum/nadd costing
   (~700 lines bespoke) is moot: ordinary ONote `+` is the paper's own output.

**Binding restatement (executed by the lap-10 order):**
- Pin 1 concludes `Zef2Prov (α + γ) e H (g ∘ f) c (Δ.erase (∃⁰ ∼φ) ∪ Γ)` — osucc dropped.
- Hypotheses gain (i) the base-additive form `∀ k, g 0 + k ≤ g k` (the exact consequence
  `noOsucc_closes` consumes; implied by `StrictMono`/(f.1) — note (f.1) p.8 states this
  consequence explicitly: "n + f(m) ≤ f(n+m)"), and (ii) the Lemma-25 cut-formula-size analog
  `φ.complexity ≤ f 0` (Lemma 25's `max{lh(C), …} ≤ f(g(0))` hypothesis; feeds the fresh
  cut-read gates at `(g∘f) 0 = g (f 0)`; available at every caller from `Zef2.cut`'s own
  `hcutRead` — the trap-8 amendment's gate exists exactly for this).
- Pin 2: same hypothesis additions; its conclusion (existential `δ`) absorbs the unbumped
  ordinal unchanged.
- ⚠️ Latent seam flagged for the grind, NOT resolved here: E–W's relativization is
  addition-based (`f[n](m) = f(n+m)`, which PRESERVES (f.1) — p.9) while the repo's `rel1` is
  max-based (`f (max n m)`, which does NOT preserve strictness/base-additivity). The pins' TOP
  slots are never rel1-relativized so the restatement is safe, but the pass grind (laps 11+)
  will meet this at ω-nodes. Known escapes: thread only Monotone+infl through the recursion
  (the P1 lift already showed they suffice for the lift), or a judged rel1→addition-based
  amendment. The lap-10 probe documents which is needed; it does not decide.

## 4. Trap 10 — the ladder statements (judge-caught; L-D and L-W VOID)

- **L-D `readoff_delta0_Zef2` VOID.** Its hypothesis `hφbdd` is a classical tautology
  (`fun n _ => Classical.em _` discharges it — it carries zero content), and `matrixTrue` is a
  bare `Form → Prop` parameter. Instantiate `matrixTrue := fun _ => False`: the pin then asserts
  no rank-0 `Zef2` derivation of any `{∃⁰ φ}` exists — false the moment the pipeline produces
  one, vacuous otherwise. Undischargeable under full-discharge-or-abandon. **Corrected shape**
  (lap-10 order): evaluator = the repo's `atomTrue` — its DEFINITION
  (`Semiformula.Evalm ℕ …`) already evaluates arbitrary closed formulas, the atom restriction
  lives only in the name — plus a syntactic boundedness hypothesis on the instances (repo-native
  Δ₀/open-formula predicate chosen at the statement lap with a mini-probe); conclusion
  `∃ n ≤ f 0, atomTrue (φ/[nm n])`.
- **L-W `wainer_splice_Zef2` VOID.** Trivially dischargeable as stated: take `o := 0`; from the
  hypothesis `ewIter … ≤ N` and `N ≤ fastGrowing 0 N` the conclusion follows in one line — no
  rung consumed. A pin whose discharge is free is no decomposition. **Corrected shape**: the
  splice pin IS the axiom's statement as a theorem —
  `(𝗣𝗔 ⊢ ↑goodsteinSentence) → ∃ o : ONote, o.NF ∧ EventuallyLE Dom.goodsteinLength
  (fun n => fastGrowing o n)` — consuming rungs E/R/D + the banked Hardy Lemma-19 brackets,
  composition REAL where the rung statements allow, `sorry` only at rung consumption.
- **L-E: the escalation is HONORED** (the box correctly refused to improvise the translation
  binding and said so) — but the erected placeholder
  (`∀ Γ_G, ∃ B α d H, Zef2 α e H (ewRootSlot e B) d Γ_G`, no source hypothesis) asserts EVERY
  sequent derivable, including the empty one — calculus inconsistency. VOID as a pin; the
  lap-10 order deletes it (docstring TODO remains). **Direction**: rung E gets its OWN
  statement lap. Statement = the W3-ratified K-hypothesis shape re-based onto `Zef2`, with
  `hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence` as the source hypothesis and `Γ_G` bound to the CONCRETE
  goodstein translation — homed in a NEW leaf module (e.g. `WainerLadder.lean`) importing both
  `OperatorZef2` and the translation apparatus. The "would cross-import" concern dissolves in a
  new leaf; `OperatorZef2.lean` stays translation-free.
- **MANDATED rung-E pre-probe (trap-11 pre-emption).** `Zekd` carries the true-atom axioms
  (`trueRel`/`trueNrel`, `OperatorZinfty.lean:51/53`); `Zeh`/`Zef`/`Zef2` have NONE — and E–W's
  Def 23 includes **(Ax2) `Γ ∩ TRUE₀ ≠ ∅`** literally. If the PA-axiom leaves of the embedding
  need true-atom leaves (the standard design, and the W3 shape was ratified on the Zekd lane),
  `Zef2` as it stands cannot receive the embedding. The rung-E statement lap MUST kernel-probe
  this adequacy question first. If Ax2 constructors must be added to `Zef2`, that is a judged
  calculus amendment with a known cost: `toZef` breaks (Zef lacks the constructors), so both
  read-off pins lose the forgetful discharge and need native re-proof over `Zef2` (templates
  exist: the proven Zef read-off and the Zekd read-off both case-split on `atomTrue` already).

## 5. Ratified content

`Zef2.toZef` (real 6-case induction, conservativity witness) + both read-off discharges by
reuse (zero re-proof, as mandated) · `Zef2.gate` projection · `allInv_Zef2` (real, gate
re-threaded via `gate_rel1`) · inversion-suite deferral (orInv/andInvL/andInvR) RATIFIED as
prudent given the pins restatement in flight — port them when consumed · ewN arithmetic bank ·
`collapseIter`/`ewIterTower` (composition direction checked: pass `d+1` iterates the towered
slot at the `d`-collapsed ordinal — correct) + `collapseIter_NF` real · L-R `rankToZero_Zef2`
statement per the order verbatim · ledger-14 citation row update · the lap-9 initiative
(attacking the crux instead of the rung-R plumbing fallback) was in-authority (wip-only) and
productive — the probe pair is exactly what this ruling needed.

## 6. Process notes

- Codex provenance ×2, no preamble: content-conformant both laps, and lap 8 committed its own
  work — an improvement over lap 7. The self-run gate claims were nonetheless treated as
  unverified and re-run from scratch (all reproduced).
- Statement-trap ledger: **ten traps (1–10) caught at statement/probe/judge time; zero have
  reached a grind-lap discharge.** Trap 9 = the reduction-gate osucc/+1 (lap-8 isolated,
  lap-9 kernel-sharpened, judge-resolved paper-literal). Trap 10 = the ladder-erection
  statement defects (L-D/L-W, judge-caught; L-E placeholder voided alongside). The lap-7
  ruling's "pre-empted ninth trap" (arbitrary-`Zeh` transport) was never erected and consumes
  no number.
- The lesson of trap 9 is the lesson of trap 8 verbatim: the deviation from the paper's
  literal form (there the fs-recursion shortcut, here the osucc bump) is exactly what dies.
  Rulings that cite the PDF page beat rulings that remember it.

## 7. Gate state after this pass

- Build 🟢 1341 · headline quadruple UNDRIFTED · `blueprint_audit` 16/16 · src sorries =
  old pin 3 + the 7 disclosed `OperatorZef2` pins (two of which — L-D, L-W — are VOID pending
  their lap-10 restatement; L-E pending deletion) · wip evidence read-only.
- **Next fire: lap 10** per `REBUILD-Z-LAP10-ENTRANCE-2026-07-02.md` — the α+γ seam probe,
  the judged restatements (pins 1–2, L-D, L-W, L-E deletion), then the pins 1–2 grind
  (probe-gated, same fire). The pass stays FORBIDDEN.
