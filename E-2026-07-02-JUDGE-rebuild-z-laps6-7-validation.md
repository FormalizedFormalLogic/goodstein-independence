# E — JUDGE validation of REBUILD-Z laps 6–7 run (Ren, 2026-07-02)

> Judge pass over the cap-bounded treadmill run fired after the lap-5 ruling (single grind lap —
> lap 6, global 186; the run terminated at the trap-8 terminus and never opened a lap 7). Baseline
> for all freeze checks: **`d86285c`**. Run commits judged: `c39f08e`..`d820ceb` (11).
> Companion architect order issued with this ruling: `REBUILD-Z-LAP7-ENTRANCE-2026-07-02.md`.

## 1. Verdict: **PARTIAL PASS + the EIGHTH statement trap RATIFIED — pin 3 is ARCHITECT-GATED**

Item 1 of the ratified order (discharge the C5 pin `iterSlot_monotone`) is **DISCHARGED and
ratified**. Item 2 (the pass induction) correctly terminated in an **escalation, not a discharge**:
the locked pin-3 output slot (the lap-5-amended diagonalizing `iterSlot f α`) is
unprovable-as-stated, kernel-anchored, statement-intrinsic. This is the eighth statement trap and
the second caught by a grind lap doing exactly what the process demands — stopping at a locked form
it believes wrong instead of bending it. **Eight statement traps caught at statement/entry time;
zero have reached a grind-lap discharge.** The `(iterSlot, fs-recursion)` C2 shape is DEAD; the
architect ruling (§5) supersedes it. No re-fire against the current pin-3 form.

## 2. Independent re-verification (kernel-grounded, all run by this judge)

- **Freeze check vs `d86285c`** (`git diff` on `src/GoodsteinPA/OperatorZeh.lean`, every hunk
  inspected): exactly two hunks. (1) §5b: `iterSlot_monotone`'s `sorry` body replaced by a real
  proof + two NEW helper theorems (`iterSlot_le_of_reaches`, `iterSlot_le_of_lt`); the theorem's
  signature is UNTOUCHED — both hypotheses (`hf_mono`, `hf_infl`) retained, no α-restriction, no
  dodge hypotheses. (2) Pin 3: docstring-only annotation (the LAP 6 FINDING block); statement
  tokens verbatim. No hunk touches `iterSlot`/`collapse` defs, pins 1–2, `Zeh`/`Zef` inductives,
  `ZehProv`/`ZefProv`, `zeh_to_zef`, or the read-off. `git diff --stat`: no other `src/` file
  changed. Freeze: **CLEAN**.
- **Build**: `lake build` green, **1333 jobs**; the sole OperatorZeh sorry warning is
  `cutElimPass_Zf` (:1907).
- **Sorry accounting**: OperatorZeh = exactly **1** (pin 3; down from the baseline's 2 — the C5
  pin discharged). No new sorries anywhere in `src/`.
- **Axiom sweep** (own scratch, `lake env lean`): headline `peano_not_proves_goodstein` =
  `[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]` — **NO DRIFT**.
  `iterSlot_monotone` / `iterSlot_le_of_reaches` / `iterSlot_le_of_lt` =
  `[propext, Classical.choice, Quot.sound]` (axiom-clean). `cutElimPass_Zf` +
  `cutElimPass_exit_root` = sorryAx-bearing (expected; pin open).
- **Rails**: no `iterCount` resurrection (`git grep` clean); no `mono_e`-shape; no new `axiom`s or
  `native_decide` in the `src/` diff; existentials root-only untouched.
- **`blueprint_audit`**: PASSES — 15 nodes consistent (with the parallel session's uncommitted
  WainerRoute attributes 14–15 in the working tree).
- **`wip/Trap8Probe.lean`**: recompiled clean by this judge (`lake env lean`). The sharp
  impossibility `no_fixed_arg_monotone_unbounded_slot` is a **pure kernel proof** (no
  `native_decide`); the value lemmas use `native_decide` (correct tool — WF-recursive `iterSlot`
  does not kernel-reduce), same evidence grade as the ratified trap-7 probe.

## 3. Item 1 RATIFIED: `iterSlot_monotone` discharged + two banked levers

The proof is the honest one the order demanded: `monotone_nat_of_le_succ`, WF recursion on `α`
(`termination_by α`), and the LIMIT case pays the index step through
`iterSlot_le_of_reaches (fastGrowing_bachmann_reach e n)` — the `hardy_monotone` /
`hardy_le_of_reaches` mirror, with the successor argument-shift absorbed by inflationarity.
No extra hypotheses, no α-restriction (the VOID-detection items on this pin's rubric): checked
against the diff directly. `iterSlot_le_of_lt` (budgeted ordinal-monotonicity: `β < α`, NF, and
`norm β ≤ x` give `iterSlot f β x ≤ iterSlot f α x`) is sound and judged on its merits.

**Carry-forward caveat (honest bookkeeping):** these three theorems are about the fs-recursion
`iterSlot`, which the §5 ruling retires. Their forward value is the proof TEMPLATE (the
reaches-transfer pattern the `ewIter` lemmas will mirror) and the kernel evidence they encode —
not direct reuse. The trap-8 doc's "needed by ANY slot form" claim is overstated under the E–W
redesign; the discharge is ratified as faithful execution of the ratified order regardless.

## 4. The EIGHTH statement trap RATIFIED (kernel evidence verified, premises checked against the frozen surfaces)

The escalation's §3 "statement-intrinsic" argument is **not a strawman** — every premise is a
verbatim fact of the locked code, checked by this judge:

- `Zef.exI` carries `hbound : n ≤ f 0` — the slot read at argument **0** (OperatorZeh :1402);
- `Zef.mono_f` is the ONLY slot-changing move and requires **pointwise** `∀ x, f x ≤ f' x`
  (:1420); slots only raise;
- `ZefProv` slackens only the HEIGHT, never the slot (:1465);
- pin 3's conclusion pins the output slot **rigidly** to `iterSlot f α` (:1910).

The kernel evidence: `trap8_mono_f_lift_fails` / `trap8_dips_at_limit_base` (the dip
`iterSlot f ω 0 = 2 < 3 = iterSlot f 2 0` at `f = ·+1`), the sharp
`no_fixed_arg_monotone_unbounded_slot` (NO fixed-argument slot map is both ordinal-monotone and
unbounded on the finite ordinals — pure kernel proof), `trap8_budget_not_norm_alpha`,
`no_count_bounds_subnorms`. All recompiled by this judge. Note the trap-7/trap-8 conflict is
genuine and irreducible **at fixed reading argument**: trap 7 (ratified) forces growth along the
ordinal; trap 8 forces monotonicity for the lift; the sharp lemma proves no fixed-argument read
satisfies both.

**Two judge corrections to the escalation record** (neither changes the verdict):

1. `Zef.cut` carries **no direct slot-read** (:1404–1409 — no `f`-clause); its exposure is the
   `mono_f` lift of its two sub-derivations only. The doc's "`exI`/`cut` witness bound at 0"
   phrasing overcounts; the immovable argument-0 read is `exI`'s alone.
2. The §8 terminus — "closing trap 8 faithfully may require relativizing the `exI`/`cut`
   witness-read" — is **SUPERSEDED** by the architect ruling (§5). E–W's own calculus keeps the
   witness read at argument 0 (Def 23's (⋁): `N(ι₀) ≤ f(0)`); what the repo's rendition is
   missing is different (and smaller per-rule, larger per-judgment): the judgment-level norm side
   condition + the norm-gated max form of the iterate.

**Also ratified:** the calibration note that the trap-7 fix (the lap-5 JUDGE amendment — the
fs-recursion diagonalizing iterate) is what CONTAINED trap 8. The lap-5 ADDENDUM's "T-Z5(iii) is
resolved at statement time" was wrong; the fs-recursion realization of E–W Lemma 19 was a
shortcut past the paper's actual Def 16, and the eighth trap is the bill. Charged to the judge
seat, not the box.

## 5. The architect ruling (paper-grounded): E–W Def 16 + Def 23, taken literally

Read against the PDF (pp. 8–12), not just the on-disk summary. E–W reconcile exactly the
trap-7/trap-8 tension with two coupled devices, neither of which is the current `Zef`/`iterSlot`
shape:

1. **The iterate is a norm-gated MAX, not fs-recursion** (Def 16):
   `f^α(m) = max{ f^β(f^β(m)) | β < α, N(β) ≤ f(N(α)+m) }` (base `f^0 = f`). It cannot dip: it
   dominates every gate-admissible `f^β` by construction (Cor 17.2).
2. **Every judgment node carries the norm side condition** `N(α) ≤ f(0)` (Def 23's HYP —
   "doubly controlled"). So any sub-derivation ordinal β satisfies `N(β) ≤ f(0) ≤ f(N(α)+x)`
   for ALL x — the gate holds everywhere, giving the **pointwise** lift
   `f^β ≤ f^α` unconditionally for admissible sub-derivations. The sharp impossibility
   dissolves precisely here: monotonicity is only ever needed on the norm-bounded (finite)
   admissible family, so it never meets unboundedness.
3. **The witness read stays at argument 0** (Def 23's (⋁): `N(ι₀) ≤ f(0)`); `Zef.exI`'s read
   position was never the defect.

**Judge kernel probe closing the remaining fork** (`wip/JudgeTrap8FixProbe.lean`, compiles
clean): the side condition ALONE does not rescue the fs-recursion iterate — at `f = ·+2` the
trap-8 instance is admissible (`norm 2 = 2 ≤ 2 = f 0`) and the dip persists
(`iterSlot f ω 0 = 4 < 6 = iterSlot f 2 0`; the fs-form rides `ω[0] = 1` no matter how large
`f` is). And the iterate form alone (without the side condition) is killed by
`no_fixed_arg_monotone_unbounded_slot`. **Both changes are needed; they are one design.**

The full constraints, lap plan, pre-registered triggers, and the mandatory kernel pre-probes
(anti-trap-9 gate) are in **`REBUILD-Z-LAP7-ENTRANCE-2026-07-02.md`** — lap 7 is a WIP-ONLY
statement lap (src untouched; the src surgery is a judged port afterward, per the
lap-184 → laps-2–4 precedent, because pins 1–2 and the whole `Zef` substrate re-prove on the
amended judgment).

## 6. Process notes

- **Exemplary run.** The box discharged the ordered item, hit the wall, escalated with kernel
  evidence, sharpened the finding twice (the sharp impossibility; the §8 frozen-surface
  analysis), prototyped only in wip, and stopped — no self-ratification, statement untouched
  (freeze-verified). This is the process working as designed.
- The run was cap-bounded `--max-laps 3` but correctly consumed only one lap and signalled
  `box done --green` — a wall is a lap-terminal state, not something to re-grind.
- **Blueprint attribute for `iterSlot_monotone`: DEFERRED** (judge decision). It is a brick under
  the `zeh_pass` blueprint node (which stays `notready` until pin 3 discharges), not its own
  content.tex node; and ledger ids 14–15 are the parallel session's uncommitted working-tree
  state — allocating 16 now invites an id race for no display gain. The eventual pass flip
  carries it.
- Estimates culture: the statement-lap/judge cadence stays 1-session-accurate (this run: 1 lap to
  the wall, correctly). The 2–4-session pass-grind estimate now restarts on the amended calculus
  and should be re-based after the lap-7 statement lap.

## 7. Gate state after this pass

- Build 🟢 1333 · headline quadruple UNDRIFTED · OperatorZeh sorries = 1 (pin 3, disclosed) ·
  `blueprint_audit` 15/15 · rails R1/R2/R5 intact · no new axioms.
- Pin 3 (`cutElimPass_Zf`): **ARCHITECT-GATED — grind on the current locked form FORBIDDEN**
  (kernel-refuted). The statement lives on in src untouched until the judged lap-8 port.
- Frozen surfaces: unchanged set (pins 1–2, `Zeh` core, `Zef` + `zeh_to_zef`, read-off,
  `iterSlot`/`collapse` defs + the three §5b lemmas now join the frozen ledger as evidence);
  hash-checked next judge pass.
- Next fire: **lap 7 statement lap** per `REBUILD-Z-LAP7-ENTRANCE-2026-07-02.md`
  (`--max-laps 1`, wip-only).
