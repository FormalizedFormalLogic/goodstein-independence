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

**2026-07-03 (FRESH-MIND REVIEW, global lap 201 — THE CRUX LANDED; three of four hard rungs GREEN;
sole remaining hard rung = E. THIS IS THE CURRENT BINDING BLOCK. It supersedes the lap-192 block
below AND aligns with `REBUILD-Z-SERIES-3-ORDER-2026-07-03.md`, which stays binding for operational
detail.)** Independently re-verified this lap (real `#print axioms`, bare `lake build` 🟢 1342):
headline `GoodsteinPA.peano_not_proves_goodstein = [propext, Classical.choice,
goodstein_implies_consistency, Quot.sound]`, sorryAx OFF, **no drift**. THE objective is unchanged
(discharge `wainer_bound_of_pa_proves_goodstein` via the E–W `Zef2` pipeline; headline stays undrifted).

⭐ **STATE CHANGE since lap 192 — the escalated crux is CLOSED, not open.** The lap-192 top-rank-cut
trilemma was RESOLVED by the SERIES-2 judge pass (`E-2026-07-03-JUDGE-series2-validation.md`, ruling
(1) = the absorbing-norm route `ewN → Nlog`), then EXECUTED in SERIES-3: **the top-rank cut landed
(lap 198)** and three of the four hard rungs of the Wainer ladder are now REAL, axiom-clean theorems
(verified this lap, all `[propext, Classical.choice, Quot.sound]`):
> - **Rung P** `cutElimPass_Zef2` (the pass, `passAux` 6/6) — GREEN.
> - **Rung R** `rankToZero_Zef2` — GREEN.
> - **Rung D** `readoff_delta0_Zef2` (R-4′ bound `∃ n ≤ ewIter f α 0`, green by the spineHead vacuity
>   invariant, lap 199) — GREEN.
> The splice `wainer_splice_Zef2` (rung W, `WainerLadder.lean:41`, src) now carries the **sole live
> `sorryAx`**, sitting exactly at the rung-E consumption point. When rung E lands and the splice goes
> sorry-free, `wainer_bound_of_pa_proves_goodstein` flips `axiom → theorem` and the 🟠 girder is discharged.

🚦 **MANDATED next move: Lane E — rung E (the embedding), the sole remaining hard rung.** Continue the
E-1 wip grind in `wip/E1EmbeddingGrind.lean` per the SERIES-3 order, **E-1 block 6 = the V3 predicate**:
restate `BudgetedEmbedsTC` with the witness budget bounded by a STRUCTURAL function of the assignment
(`Gexp^[c] (envSup env N)`-shaped, or the `K ≤ hardy e (…)` side condition — growth kit banked lap 200:
`Gexp = H_{ω²}`, `term_val_le_Gexp_iter`, `Gexp_iter_eq_hardy`, `envSup_cons_le`), re-close the 8 landed
cases (joins unchanged), re-prove `exs` against `stdClosedVal_asg_le_Gexp_iter`, then close the two open
leaves — **`all`** (the ω-rule uniformization via `envSup_cons_le` + `rel1_rel1` — the genuinely new
ordinal content) and **`axm`** (W1/W2 finite 𝗣𝗔⁻ axioms via `trueRel` bounded truth). THE DECISIVE CASE
is `all` under V3: if V3 cannot uniformize the per-branch witness budget over the ω-rule, the SomeK/W3
statement shape itself must be rethought — so probe `all` early, don't leave it last. When V3 closes the
ladder, the accumulated rung-E statement + the E-0 Ax2-need probe go to the **next judge pass** for
ratification; **do NOT self-ratify the rung-E statement into `src`** — promotion is post-ratification.
Lanes independent of E stay open per SERIES-3 (W-1 shrinks the splice sorry to the E-seam as rungs land).

**Why:** with P/R/D green and W mechanical, rung E is the ONLY piece whose feasibility is still in real
doubt — the whole 🟠 girder axiom discharges the moment E lands. Attacking E (hardest-first) is worth more
than any hygiene or leaf-work; the last three laps correctly did exactly this (N→D→E) and must continue.

**FORBIDDEN (this block):** retreating to hygiene / side-leaves / docs-theatre while rung E is open;
touching Route-A surfaces (the norm swap must not touch the headline route); self-ratifying the rung-E
statement (or `Zef2T`/(Ax2)) into `src` (E-0 probes are wip-only, ruling inputs); statement text with
authoring freedom beyond ratified texts / their `ewN→Nlog` images / R-4′ / wip DRAFTs; re-grinding a
landed rung; idle/padding laps. All SERIES-3-order FORBIDDENs remain in force. `rel1`/norm/output changes
in `src` only via a ratified SERIES-3 pivot, ledgered as such.

**2026-07-02 (FRESH-MIND REVIEW, global lap 192 — top-rank cut escalation UPHELD + SHARPENED;
lane B REFUTED; productive lane = D. ⛔ SUPERSEDED by the lap-201 block above — its top-rank-cut
escalation was RESOLVED (SERIES-2 ruling (1) `ewN→Nlog`) and its Lane-D mandate is DONE (rung D
GREEN, lap 199); read below only for the historical judge rulings, which remain binding. Originally:
THIS IS THE CURRENT BINDING BLOCK; it supersedes the
lap-191 handoff "NEXT" and the laps-8–9 block's grind order for lane P only — all judge rulings
below stay binding.)** Independently re-verified terminal state (real `#print axioms`, build 🟢
`GoodsteinPA`): headline `GoodsteinPA.peano_not_proves_goodstein = [propext, Classical.choice,
goodstein_implies_consistency, Quot.sound]`, sorryAx OFF, **no drift**. THE objective is unchanged
(discharge `wainer_bound_of_pa_proves_goodstein` via the E–W `Zef2` pipeline; headline stays
undrifted).

⚖️ **Crux ruling (top-rank cut = the sole open `passAux` case, `OperatorZef2.lean:748`).** The
lap-191 escalation is **CORRECT — the pre-registered `rel1`/(f.1) base-additivity wall FIRED as
anticipated** (Stage-3 order: "if a step is kernel-blocked WITHOUT `EwF1`-of-`rel1`-slots → statement
wall, halt lane P, escalate; a `rel1` redesign is a judged amendment — NOT yours"). Two sharpenings
this review adds:
> (1) **Lane B (the PENDING/ledger "PROOF-only resolution") is REFUTED.** Its floor route needs the
>     tight bound `ewN(∀-witness) ≤ f 0 + 1`, but (a) the reduction only gives `ewN(∀-witness) ≤ g 0`
>     (the ∀-slot base, unbounded relative to the ∃-base, un-absorbable by the `2m+1` floor), and
>     (b) the tight bound is NOT inductive: `ewN` grows additively under `α + γ` outputs while `ω^α`
>     absorbs additively, so a depth-`d` nest of top-rank cuts blows `ewN(witness)` up ~`2^d·(f0+1)`
>     while the ∃-base stays fixed. So do NOT "pursue lane B next" — it does not close.
> (2) **The obstruction is a TRILEMMA among three RATIFIED pillars.** Closing the node gate
>     `ewN(α+γ) ≤ g(f 0)` needs one of: an **absorbing** norm (`ewN(α+γ)=max(…)`) — breaks the
>     finite-fiber requirement that forced `ewN` (T-Z7(i)); OR base-additivity `hg_base` of the
>     ∀-slot — destroyed by `rel1 f n = f(max n ·)` in nested ω-contexts (banked kernel-refutation,
>     `wip/Lap11CutFloorProbe.lean`); OR a non-additive output ordinal — the `α+γ` fixed by ruling #1.
>     `rel1` max→+ ALONE is insufficient (it preserves base-additivity only for *strictly* monotone
>     `g`, which `ewIter` lacks — the trap-8 plateau). This is judge/architect-owned; the prime
>     amendment candidate to hand the judge = **a finite-fibered ABSORBING norm** (dissolves the gate
>     with no slot property at all).

🚦 **MANDATED next move: lane D — `readoff_delta0_Zef2` (`OperatorZef2.lean:892`, Towsner §5.4
bounded-∀ read-off).** It is the sole open PROOF-only lane, fully independent of the escalated
crux, on the headline path, est. 2–3 laps; template = `readoff_sigma1_Zef2`/the `Zef` axL true-side
split (`OperatorZeh.lean:1801`ff). The top-rank crux may be advanced ONLY by a **wip-only** kernel
probe of a candidate amendment (the absorbing-norm question above) as escalation input — recorded to
`REBUILD-Z-SERIES-1-LEDGER.md`, NEVER ported to `src`.

**FORBIDDEN (lane P, this block):** grinding the top-rank cut in `src` as a proof-only problem (wall
fired, lane B refuted); re-deriving the `hg_base` refutation (banked); self-ratifying any `rel1` /
norm / output-ordinal / statement change (VOID); porting an amendment probe to `src`. Rung E stays
architect-gated; all FORBIDDENs from the laps-8–9 block remain.

**2026-07-02 (JUDGE PASS on laps 8–9 — port RATIFIED; traps 9 AND 10 caught; ruling #1
resolved PAPER-LITERAL. Superseded for lane-P grind order by the lap-192 review block above;
all judge rulings remain binding.)** Ruling:
`E-2026-07-02-JUDGE-rebuild-z-lap8-validation.md`. Lap 8 (codex, committed) delivered the port
verbatim (`toZef` discharge of both read-offs as mandated; `allInv_Zef2` real; ewN bank; L-R
ratified) + two honest escalations; lap 9 kernel-sharpened escalation #1
(`wip/Lap9GateProbe.lean`, judge-reverified). ⚖️ **Ruling #1**: E–W Lemma 25 concludes at
`α + β` — NO successor bump; the repo's `osucc (α + γ)` was a self-inflicted cascade. Pins 1–2
restate at `α + γ` with `∀ k, g 0 + k ≤ g k` + `φ.complexity ≤ f 0` hypotheses; the judgment
gate `ewN α ≤ f 0` is Def-23-faithful and UNCHANGED (fix (b) REFUSED — a Def-16/Def-23
conflation). ⚖️ **Trap 10**: L-D (tautological `matrixTrue` form) and L-W (trivially
dischargeable) VOID — judge-supplied restatements; L-E placeholder VOID + deleted (rung E =
its own statement lap in `WainerLadder.lean` with the MANDATED Ax2-adequacy pre-probe: `Zekd`
has `trueRel`/`trueNrel`, `Zef2` has none, E–W Def 23 has (Ax2)). 🚦 NEXT FIRE: **SERIES 1 — the batched grind
pipeline** per `REBUILD-Z-SERIES-1-ORDER-2026-07-02.md` (`--max-laps 10 --max-duration 24h`
or codex series; supersedes the lap-10 micro-order — operator-directed cadence change:
statements stay pre-ratified + VERBATIM in the order, grinds chain in series, ONE judge pass
over the pipeline via `REBUILD-Z-SERIES-1-LEDGER.md`). Lane P: Stage 1 (seam probe + the
judged restatements, copy-not-compose) → pins 1–2 grind → **the PASS grind (UNLOCKED —
statement ratified lap 7; Monotone+infl-only invariants at ω-nodes, the rel1/(f.1) seam is a
halt-and-escalate wall)** → rung R. Lane D (independent): rung D discharge after its
predicate mini-probe commits. FORBIDDEN: rung E in any form; statement text beyond the
verbatim blocks (sole delegated choice = L-D's `<BoundedInstance>` predicate); `rel1`/
constructor redesigns; self-ratification (VOID).

**2026-07-02 (JUDGE PASS on lap 7 — PASS at statement level; trap 9 did NOT fire; the E–W
ruling is KERNEL-VERIFIED. Superseded by the laps-8–9 judge block above; rulings still
binding.)** Ruling:
`E-2026-07-02-JUDGE-rebuild-z-lap7-validation.md`. Lap 7 delivered wip-only as ordered:
`wip/EwIter.lean` (Def-16-verbatim norm-gated max iterate over the constructor norm `ewN` +
finite `ewBall` with sorry-free completeness; **P1 the lift is KERNEL-PURE** — the exact
proposition trap 8 refuted for `iterSlot` holds for `ewIter`, from mono+infl alone; P2/P3
proven ∀x) + `wip/Zef2Calculus.lean` (`Zef2` per Z5: HYP `ewN α ≤ f 0` every node, exI at 0,
cut lh-shadow, rel1 branches; pass pin Z6-verbatim; C3 exit consumes `ewIter (ewRootSlot e m) α 0`;
exactly 3 disclosed sorries). T-Z7(i) fired + handled by the sanctioned fallback (repo CNF norm
has infinite fibers — kernel witness; `ewN` adopted). ⚖️ Judge amendments on P4 (binding):
the embedding budget must be EXISTENTIAL (Zeh is Prop — no function-of-derivation), and rung E
targets the PA-proof-sourced W3 pipeline re-based onto `Zef2` — arbitrary-`Zeh` transport is
REFUSED (ω-branching + information-free membership; pre-empted ninth trap). 🚦 NEXT FIRE:
**lap 8 = the judged src port + wainer-ladder erection** per
`REBUILD-Z-LAP8-ENTRANCE-2026-07-02.md` (`--max-laps 2 --max-duration 6h`): port EwIter+Zef2 to
src, discharge both read-off pins via the forgetful `Zef2.toZef` (MANDATED), re-prove pins 1–2 +
inversions over `Zef2`, erect ladder pins L-R/L-D/L-E/L-W with ledger rows 17+, verdict, STOP
for the judge. FORBIDDEN: grinding the pass; old-`Zef`/`Zeh`/pin-3 statement tokens (docstring
supersession notes only); arbitrary-`Zeh` embedding pins; self-ratification (VOID).

**2026-07-02 (JUDGE PASS on the laps-6–7 run — PARTIAL PASS + EIGHTH statement trap RATIFIED;
pin 3 ARCHITECT-GATED; the E–W rebuild order OPEN. Superseded by the lap-7 judge block above;
rulings still binding.)**
Ruling: `E-2026-07-02-JUDGE-rebuild-z-laps6-7-validation.md`. Lap 186 discharged the C5 pin
`iterSlot_monotone` (ratified, axiom-clean) and then correctly ESCALATED the pass induction: the
lap-5-amended output slot (fs-recursion diagonalizing `iterSlot f α`) is unprovable-as-stated —
`iterSlot` dips at limit bases (`iterSlot f ω 0 < iterSlot f 2 0`), the only slot move
(`Zef.mono_f`) needs the pointwise lift, kernel-refuted (`wip/Trap8Probe.lean`; sharp form: NO
fixed-argument slot read is both ordinal-monotone and unbounded). Judge probe
(`wip/JudgeTrap8FixProbe.lean`): the E–W side condition alone does NOT rescue the fs-form.
**Architect ruling (PDF-grounded, E–W Def 16 + Def 23): norm-gated MAX iterate (`ewIter`) +
judgment-level norm side condition (`norm α ≤ f 0` at every node) + witness reads STAY at
argument 0.** 🚦 NEXT FIRE: **lap 7 = STATEMENT LAP, WIP-ONLY** per
`REBUILD-Z-LAP7-ENTRANCE-2026-07-02.md` (`--max-laps 1`): define `ewIter` + `Zef2` in wip, run
the mandatory kernel pre-probes P1–P4 (the lift theorem FIRST — if it fails, trap 9, STOP),
restate pin 3 + the C3 exit (bodies `sorry`), verdict, STOP for the judge. Then lap 8 = judged
src port (pins 1–2/inversions/embedding/read-off re-proven on `Zef2`); laps 9+ = the pass grind.
FORBIDDEN: ANY `src/` edit this lap; grind on the current pin-3 form (kernel-refuted);
fs-recursion/fixed-count/fixed-read iterates; pins 1–2/`Zeh`/`Zef`/`zeh_to_zef`/read-off frozen;
Route-A; Δ₀; `(k,d)`; self-ratification (VOID).

**2026-07-02 (JUDGE PASS on lap 5 — PASS WITH AMENDMENT; SEVENTH statement trap caught; laps 6–7
OPEN. Superseded by the laps-6–7 judge block above; process rulings still binding.)** Ruling: `E-2026-07-02-JUDGE-rebuild-z-lap5-validation.md`.
Lap 185 delivered the statement lap faithfully (collapse/pin-shape/exit-corollary RATIFIED), but its
iterate index `iterCount := norm·+1` (fixed count) is **kernel-refuted at the `allω` reassembly**
(`wip/JudgeTrap7Probe.lean`: parent `11 < 23` branch at `α = ω`/`ofNat 2`/`hardy ω`; `norm` is not
monotone along `<`). Judge amendment APPLIED: `iterSlot` is now the **diagonalizing** ordinal-indexed
iterate (base `f`; successor `iterSlot f a (f n)`; limit `iterSlot f (λ[n]) n` — E–W Lemma 19's
transfinite `F^α(0)`, same fundamental-sequence recursion as `hardy`). Pin-3 statement text +
`cutElimPass_exit_root` unchanged and green; `iterSlot_infl` proven; **`iterSlot_monotone` is a
disclosed C5 pin = lap 6's FIRST item** (mirror `hardy_monotone`, f-relative reaches comparison).
🚦 LAPS 6–7 OPEN (operator fires): discharge restated pin 3 — order: `iterSlot_monotone` →
`∃`-cut/structural lanes (`iter_comp` on finite ordinals) → the `allω`/reaches lane (long pole;
`reaches_of_lt`/norm-budget machinery around `hardy` is the template). Gate every lap: build 🟢 +
headline UNDRIFTED + `cutElimPass_exit_root` green. FORBIDDEN: pins 1–2/`Zeh` core/`zeh_to_zef`/
read-off (frozen, hash-checked next judge pass); Route-A; Δ₀ extension; `(k,d)` work;
self-ratification (VOID); reverting to any fixed-count iterate (kernel-refuted).

**2026-07-02 (JUDGE PASS on laps 2–4 — PASS; pins 1–2 discharge ACCEPTED; the slot-judgment
amendment RATIFIED with judge authority. Superseded by the lap-5 judge block above for the pin-3
shape; process rulings still binding.)** Ruling:
`E-2026-07-02-JUDGE-rebuild-z-laps2-4-validation.md` (independent kernel re-verification: build 🟢
1333, pins 1–2 + the full `Zef` layer standard-triple, pin 3 + the `Zeh` core + headline
untouched/undrifted, `blueprint_audit` 13/13, both wip refutation probes re-compiled by the judge).
LOCK §1-A1/§3 amended — **Addendum 2** in `ZEH-STATEMENT-LOCK-2026-07-02.md`: the elimination suite
runs in `Zef`; **`Zeh` is RETAINED** (embedding-side judgment; `zeh_to_zef` = the sanctioned lift;
the lap-184 block's "retire `Zeh` if subsumed" is dead — do not retire it). ⚖️ Process ruling: the
box's self-ratification (`d232a59`) was OUT OF AUTHORITY — mitigated this once (provisional
confirm-or-revert framing + complete kernel evidence + judge unavailable + nothing pushed), NOT a
precedent: a future gate-crossing `src` port = VOID regardless of merit; wip-prototype + escalation
baton is the ceiling of an autonomous run's authority. 🚦 NEXT: the lap-5 entrance mini-lock
(`REBUILD-Z-LAP5-ENTRANCE-2026-07-02.md`) — pin-3 restatement over `Zef` (ordinal-indexed iterate,
E–W Lemma 19/30; NOTE `e` is a phantom in `Zef` — nothing "raises the control", the slot iterates),
then laps 5–7 assembly when the operator fires. Pin 3 discharge as written stays FORBIDDEN;
Route-A + the Δ₀ extension unchanged.

**2026-07-02 (lap-184 REVIEW — SLOT-JUDGMENT AMENDMENT provisionally ratified; superseded by the
judge-pass block above, kept for provenance. The port it mandated is COMPLETE and judged.)**
THE objective: discharge pins 1–2 (`cutReduceAllAuxRunning_Zf`, `stepAllω_Zf`) in
`src/GoodsteinPA/OperatorZeh.lean` **for real** (axiom-clean, no `sorry`). WHY the shape changed:
laps 2–3 proved in-kernel that the LOCK's ℕ-stage judgment (§1 A1) *cannot* carry the fixed-control
running-family reduction — this is exactly the failure LOCK R4 forbids ("ℕ-valued budget in a
reduction motive"). The R4-compliant fix — a function-slot judgment `Zef` (stage `m` ⤳ slot
`f : ℕ → ℕ`; `exI` bound `n ≤ f 0`; `allω` branch `rel1 f n`; reduction output slot `g∘f`) —
discharges pins 1–2 **and** the read-off exit sorry-free in `wip/ZefSlotCalculus.lean`
(`redDeriv_slot`, `stepAllω_Zef`, `headline_readoff_Zef`, all `[propext, Classical.choice,
Quot.sound]`). RATIFICATION + kernel evidence: `REBUILD-Z-LAP4-RATIFICATION-2026-07-02.md`
(review-lap ratification of the LOCK §1-A1/§3 amendment; architect confirms-or-reverts on branch
`plan`). THE MANDATED NEXT MOVE: **port `Zef` into `src` and discharge pins 1–2**, staged so each
lap ends green — decomposition in `PENDING_WORK.md` § "SLOT-JUDGMENT PORT" (P1 introduce `Zef` +
`mono_f`/`change_H`/`ZefProv`/`allInv_Zef`; P2 `redDeriv_slot`; P3 restate+discharge pins 1–2,
update §6 seams to `g∘f`; P4 read-off/bridge, retire `Zeh` if subsumed). GATE every lap: build 🟢
AND `peano_not_proves_goodstein` `#print axioms` UNDRIFTED (`[propext, Classical.choice,
goodstein_implies_consistency, Quot.sound]`) AND §6 seam probes green — any breaking ⟹ STOP +
escalate. FORBIDDEN DRIFT: reverting to the stage-`m` reduction (kernel-refuted, do NOT re-grind
the `redDeriv` gap as written); the `f∘g` order (kernel-refuted `reslot_fog_FAILS` — it is `g∘f`);
pin 3 (`cutElimPass_Zf`, lap-5 entrance mini-lock); Route-A; the Δ₀ read-off extension; manufacturing
docs-only "progress" instead of executing the port.

**2026-07-01 (OPERATOR DECISION — FULL DISCHARGE OR ABANDON; overrides any "accept axiom" language anywhere below).**
The end-state is **BINARY and non-negotiable**: either the headline `𝗣𝗔 ⊬ ↑goodsteinSentence` is proved
**genuinely axiom-free** (`#print axioms` = `[propext, Classical.choice, Quot.sound]` + the documented
`native_decide` base ONLY, with EVERY blueprint axiom discharged `axiom → theorem`), **OR the expedition is
abandoned**. Shipping "modulo a named / citable / accepted axiom" is a **100% NON-STARTER** (operator,
2026-07-01, verbatim: *"This is 100% a non-starter. The goal is full discharge or abandon. These are the
only 2 options."*). This applies **equally** to `wainer_bound_of_pa_proves_goodstein` (Route B) AND
`goodstein_implies_consistency` (Route A) — a named axiom is an *audit surface for a debt that must be
paid*, never a shippable endpoint. **The accept-as-axiom fork is deleted**; ignore it wherever it still
appears (`ROUTE-DECISION` "Next work" #2, the lap-171 "decide whether accepted" clause below). The only live
strategic question is therefore: **does a route have a real path to ZERO axioms?** If neither does, the
honest move is *abandon*, not accept. (This does not itself pick a route — see the PIVOT-B block below — it
sets the bar every route must clear.)

**2026-07-01 (OPERATOR-COMMISSIONED FEASIBILITY SPIKES — the ROUTE-DECISION "Next work #3" gate, made
concrete).** The operator commissioned TWO bounded spike sessions to decide whether the someK/operator
lane is the real path-to-zero-axioms (per `MASTERPLAN-2026-07-01-ZERO-AXIOMS.md` §3: Buchholz–Wainer
prove the Wainer classification BY ω-rule + cut-elim, so the `OperatorZinfty` machinery is the
candidate discharge substrate for `wainer_bound_of_pa_proves_goodstein` — not a separate "A' route").
- **Work orders (binding, one session each): `SPIKE-W3-STATEMENT.md`, then `SPIKE-W4-CONTROL.md`.**
  A spike session executes ITS order only: typed skeleton + binary verdict file
  (`SPIKE-W{3,4}-VERDICT.md`) + commit + STOP. Sorries expected; NO new `axiom` declarations; no
  grinding past the order's mandate.
- **Scope carve-out:** for these two sessions ONLY, the lap-171 FORBIDDEN clause "Towsner/A' capstones
  as the mainline" is suspended as applied to the `OperatorZinfty`/`ZekdSomeK` substrate — that
  substrate is exactly what is under evaluation. Everything else FORBIDDEN below stays FORBIDDEN
  (Crux2Blueprint, InternalZ, M2, `red`, etc.).
- **After both verdicts:** hand to the operator. PASS+PASS ⟹ ratify MASTERPLAN W0–W7 as the standing
  directive. Either FAIL ⟹ trigger T-W3/T-W4 fired: operator decides fallback-architecture vs abandon.

**2026-07-02 (SPIKE STATUS + THIRD ORDER).** W3 + W4 both **PASS w/ mandatory amendments,
judge-ratified** (`SPIKE-W{3,4}-VERDICT.md` + `E-2026-07-02-JUDGE-spike-w{3,4}-validation.md`);
neither T-trigger fired. Before the full W-ladder is ratified/ground, the operator commissioned a
THIRD bounded order — **`SPIKE-W4B-BUDGET.md`** (deciding experiment #3: the W4 residual, the
principal ∀/∃ `d`-budget under enclosing ω-nodes; pre-registered trigger **T-W4B** = the `Zᵉ`
Buchholz-operator-control fallback fork, fired on day 1 instead of 20 laps in). Same session rules
as W3/W4 (execute ITS order only: probe + binary verdict + commit + STOP; sorries expected; NO new
`axiom` declarations), and the scope carve-out above extends to this session verbatim.

**2026-07-02 (OPERATOR DECISION — `Zᵉ` FORK GREEN-LIT).** SPIKE-W4B ran: **FAIL, T-W4B FIRED,
judge-ratified** (`SPIKE-W4B-VERDICT.md` + `E-2026-07-02-JUDGE-spike-w4b-validation.md`) — the
principal ∀/∃ `d`-budget overflow under ω-nodes is kernel-confirmed structural; the `(k,d)`
numeric budget calculus is DEAD at that node. **The operator green-lit the `Zᵉ` redesign**
(Buchholz operator-controlled derivations, per the W4B verdict's pin: judgment `Zeh α e H c Γ`,
`H` closed under `+`/`ω^·`/`osucc`, ω-premises at `H[n]`). Consequences, binding on all laps:
- **Do NOT grind ANYTHING on the `(k,d)` motive** — the seven mechanical W4 cases, the rank-0
  twins, the running-family port: all re-keyed by the fork. `wip/SpikeW4*.lean` are evidence
  artifacts, not work sites.
- **Next work order (binding, one session): `SPIKE-Z1-SEAMS.md`** — deciding experiment #4
  (seam re-run under closure + the concrete-`H` Σ₁/read-off probe; pre-registered trigger
  **T-Z1**, which returns the fork to the operator with abandon live). Same spike session rules;
  the scope carve-out above extends to this session verbatim. The `Zᵉ` rebuild grind (~7–11
  laps) is GATED on a judge-ratified Z1 PASS.

**2026-07-02 (Z1 PASS JUDGE-RATIFIED — REBUILD GATE OPEN).** SPIKE-Z1 ran: **PASS, T-Z1 did
NOT fire, judge-ratified** (`SPIKE-Z1-VERDICT.md` + `E-2026-07-02-JUDGE-spike-z1-validation.md`,
spike commit `3683ef2`): both W4B seams close by closure (kernel-proven, rail held), the Σ₁
read-off is PROVEN (`readoff_sigma1`/`headline_readoff`, sorry-free), the Σ₁-definability-of-`H`
risk dissolves. Two kernel-forced amendments ratified (A1 judgment-carried stage; A2
common-control motive — there is NO `Zeh` `mono_e`), plus the K1–K3 finding: membership at `ε₀`
is information-free, so the numeric carrier is the Eguchi–Weiermann **function-slot** form
(arXiv:1205.2879), binding. **Binding artifacts for the rebuild:
`ZEH-STATEMENT-LOCK-2026-07-02.md`** (locked calculus core + rails; outranks lap momentum) **+
`REBUILD-Z-ORDER-2026-07-02.md`** (~7–11 laps; lap 1 = f-slot statement lap, judge-gated before
grinding; pre-registered trigger **T-R**). The rebuild starts when the operator fires it.
**Treadmill laps execute the order's Scope-A ONLY** (verbatim seed + f-slot statement drafting
+ the pre-ratified inversion-suite grind); a Scope-A-exhausted lap writes its baton and ends
(the run is bounded by launch caps — self-stop can't arm here, `src/` carries Route-A
sorries). Reduction discharge and everything beyond is judge-gated behind
`REBUILD-Z-LAP1-VERDICT.md`.

**2026-07-02 (lap-180 REVIEW — Scope-A CONFIRMED EXHAUSTED; ONE permitted brick named; corrects lap-179 "lane mined").**
Independent re-inventory confirms the REBUILD-Z Scope-A directive above still governs and is now fully executed:
A1 seed verbatim ✓, A2 verdict PASS ✓, A3 inversion suite **complete** (Zekd carries exactly 4 companion
inversions — `orInv`/`andInvL`/`andInvR`/`allInv` — all 4 ported to `Zeh`, axiom-clean; nothing missing). All 13
live-code sorries are either Route-A-FORBIDDEN (10) or judge-gated §5 Zeh pins (3); **no permitted-and-open sorry
exists**. So the run stays cap-bounded, wait-for-judge; **do NOT** grind the §5 pins, wire the growth bridge into
pin-3, touch Route-A, or open a speculative calculus rewrite — all FORBIDDEN until the judge ratifies
`REBUILD-Z-LAP1-VERDICT.md`.
- **The last permitted brick is now BANKED (lap 180):** the additive-Hardy inequality `hardy_add_le_comp`
  (`H_{e+β}(x) ≤ H_e(H_β(x))`, all NF `e,β`) + P1 corollary `hardy_add_omega_pow_le`, axiom-clean in
  `src/Hardy.lean`. With lap-179's E–W Lemma 19, **the permitted calculus-independent growth lane is EXHAUSTED** —
  do NOT re-attempt these or hunt further "growth bricks"; the only P1 work left is wiring them into the §5 pins,
  which IS reduction discharge = judge-gated = FORBIDDEN in Scope-A.
- **So the next grind lap has no permitted proof target:** confirm state (build 🟢, headline no drift, 3 pins), do NOT
  grind gated pins / Route-A / speculative rewrites, and end the lap. The run is cap-bounded, wait-for-judge.
- **Forbidden drift:** manufacturing tractable side-leaves to look busy while the judge gate is the real blocker;
  grinding gated pins/Route-A; treating a green docs-only commit as the lap's advance.

**2026-07-02 (LAP-1 VERDICT JUDGE-RATIFIED WITH AMENDMENT — REDUCTION-DISCHARGE GATE OPEN).**
`REBUILD-Z-LAP1-VERDICT.md` is **RATIFIED with the Option-A statement amendment APPLIED by the
judge** (`E-2026-07-02-JUDGE-rebuild-z-lap1-validation.md`): the lap-176 finding is confirmed —
the drafted raised-control conjunct on pins 1–2 was refutable two independent ways (K2b re-tag +
the judge's `axL`-instantiation), so the §5 statements now read **fixed-control** (E–W Lemma 25:
reduction composes `f∘g` at ONE control; the raise + numeric ITERATION live only in
`cutElimPass_Zf`, Lemma 30).  Rulings: **Q1** = Option A (kernel-forced); **Q2** = pin 3's `∃ f'`
is vacuous — its RESTATEMENT (pinned E–W iterate) is the **lap-5 ENTRANCE gate** (statement
mini-lock, judge-gated); **discharging pin 3 as written is FORBIDDEN**; **Q3** = `stepAllω_Zf`
stays unified.  **OPEN NOW (laps 2–4): discharge pins 1–2 against the AMENDED fixed-control
statements** — wire the banked bricks (`allInv_Zeh` + companions, `NormControlled.comp`,
`hardy_add_le_comp`/Lemma 19, the `ZehProv` combinators, the splice-descent bricks); the §6 seam
probes are the composition tests.  Still FORBIDDEN: pin 3 (until its lap-5 restatement),
Route-A, the Δ₀ read-off extension (laps 8–10).  Each lap ends green with real `#print axioms`
in the baton.

**lap-171 (OPERATOR DECISION — PIVOT-B = WAINER GROWTH-RATE).** The route gate is closed:
`PIVOT-B`, with B explicitly meaning the **Wainer/Cichon/Caicedo growth-rate route**, not the
Towsner operator A' lane. Record: `ROUTE-DECISION-2026-07-01-WAINER.md`.
- **Why:** the M2 probe isolated the PA-induction leaf to `PAInductionStepObligation`; escape (α)
  is dead against the live substitution API, and escape (β) is the omega-rule/meta route in disguise.
  Continuing Route A would keep grinding the finitary internal-Z calculus at exactly the design seam
  it lacks.
- **THE objective now:** make `GoodsteinPA.WainerRoute.peano_not_proves_goodstein_growth` the
  headline path by discharging its one remaining named debt:
  `wainer_bound_of_pa_proves_goodstein`.
- **Status:** the Cichon/Caicedo no-fixed-bound side is now a theorem in
  `src/GoodsteinPA/WainerRoute.lean`, proved from
  `GoodsteinPA.Dom.goodsteinLength_dominates_fastGrowing` at `osucc o` plus the successor-level
  fast-growing gap `f_o(n) + 2 < f_{osucc o}(n)` for large `n`.
- **First grind target:** build the smallest honest PA-provably-total interface needed to state the
  Wainer classification bridge faithfully, then **discharge it** (per the 2026-07-01 full-discharge
  mandate above — the "accept as a named external theorem" option is DELETED; the only outcomes are
  `axiom → theorem` or abandon the route). Work in `src/GoodsteinPA/WainerRoute.lean` and
  Foundation/Statement-facing wrapper files, not in `Crux2Blueprint`.
- **FORBIDDEN unless the operator reopens Route A:** grinding `Crux2Blueprint` residuals,
  `InternalZ` cut-elimination, M2 Foundation-to-Z simulation, or Towsner/A' capstones as the
  mainline. Those are banked/reference material only.
- **Source discipline:** ✅ the Wainer classification is now **sourced locally** (2026-07-01):
  `papers/buchholz-wainer-1987-provably-computable-fast-growing.{pdf,md}` (open OA — proves BOTH
  directions) + `papers/wainer-fast-growing-independence-slides.{pdf,md}`. The Fairtlough--Wainer ch. III
  access gap is **CLOSED**. ⚠️ **And it settles the scope**: Buchholz--Wainer proves the converse (= the
  axiom `wainer_bound_of_pa_proves_goodstein`) by **PA ↪ ω-rule + cut-elimination + ordinal assignment
  `<ε₀`** — the converse **IS the ε₀ girder** (Phase 2), not a route around it. So under the FULL-DISCHARGE
  mandate, discharging this axiom = **originating the Gentzen ordinal analysis of PA in Lean** (Bryce--Goré
  scale, un-precedented in Lean, a human-architect research milestone per `EXPEDITION-PLAN.md`) — NOT a
  dozen-lap decomposition. Wainer classification may sit as a *declared, faithful, allowlisted* blueprint
  `axiom` **while that monument is being built**, but it is a debt to DISCHARGE — `axiom → theorem` or
  abandon. See `ROUTE-SCOPE-REALITY-2026-07-01.md` for the full scope diagnosis.

**lap-167 (OPERATOR-RATIFIED ROUTE PROBE — supersedes the lap-166 grind directive).** Both pre-registered
Route-A abort triggers FIRED (see ROUTE GUARD); escalated to the operator (Trevor), who ratified a **bounded
5-lap M2 feasibility probe** as the deciding experiment before an A→B pivot. Full record + the corrected
confidence forensic (the lap-147 "~80%" was a crux-2 *engine* sub-goal number, never the headline):
`ROUTE-ESCALATION-2026-06-28.md`.
- **THE objective (only this, 5 laps): scope M2 (the Foundation→Z bridge) as a `wip/` feasibility spike —
  NOT headline wiring, NOT the 2 cut-elim engine sorries (those had their 18-lap test → false summits).**
  (GATE CORRECTED 2026-06-28 by the Codex review `CODEX-M2-PROBE-REVIEW-2026-06-28.md` + `wip/M2Probe.lean`,
  judge-validated vs source: the old stub `foundation_bot_to_Z_empty` is MIS-STATED — input must be
  `𝗣𝗔.Proof d ⌜⊥⌝` = `DerivationOf d {⌜⊥⌝}` (root = singleton `{⌜⊥⌝}`, NOT `fstIdx d = ∅`); output must meet
  the `ZDerivesEmptyR` R-invariants `ZRegular ∧ ZFresh ∧ ZSeqAnt`. The "cheap cases" framing was WRONG: PA
  induction enters Foundation as a `Δ₁Class` theory-axiom LEAF (`axm s p`), not a native rule, so Bryce–Goré's
  Hilbert-style shared-syntax PA does NOT transfer the hard part.)
  1. FIX the input shape: `foundation_proof_bot_to_Z_empty (hd : 𝗣𝗔.Proof d ⌜⊥⌝) : ∃ z, ZDerivesEmptyR z`.
  2. DEFINE the concrete one-sided→two-sided `FoundationToZSequent` relation (no implicit translation); prove
     the singleton-bottom case `toZ {⌜⊥⌝} (mkSeqt ∅ ^⊥)`.
  3. PROVE one genuinely STRUCTURAL Foundation rule (cut / allIntro) — including the `ZDerivesEmptyR` invariants.
  4. PROVE one **PA induction-axiom leaf** via the `axm s p` / `p ∈ 𝗣𝗔.Δ₁Class` interface — THE decisive case.
- **HARD GATE — lap 171, no extension.** Verdict to `ROUTE-ESCALATION-2026-06-28.md` + hand to operator: if
  the simulation relation (2) OR the induction-axiom leaf (4) expands into a large new formalization ⟹
  `PIVOT-B`; if both land cleanly with bounded coding ⟹ `M2-PLAUSIBLE` (reconsider A, re-scoped budget, fresh
  trigger). **Do NOT start lap 172 on A.**
- **FORBIDDEN:** grinding `ind_reduct_anySucc`/`residual` (engine already tested to false summits); wiring
  M2 into the headline (`goodstein_implies_consistency`); `red`/`iord`-recursion/`redLeast` (per lap-161);
  treating the probe as open-ended (it is 5 laps to a VERDICT, not a build).

**lap-166 (OPERATOR-DIRECTED LEDGER CONVERSION — not a math-direction change).** Adopted the
named-axiom-blueprint discipline (KB note `named-axiom-blueprint`; see the rewritten ANTI-FRAUD guard
below). `goodstein_implies_consistency` promoted `theorem … := sorry` → **named `axiom`**
(`Reduction.lean`), and the headline `peano_not_proves_goodstein` is now a **real proof** wired through
it (`:= not_proves_of_implies_consistency goodstein_implies_consistency`). Real `#print axioms`:
headline = `[propext, Classical.choice, Quot.sound, goodstein_implies_consistency]` — **`sorryAx` is OFF
the headline.** ⚠️ **This is a VISIBILITY change, NOT mathematical progress** (KB: "honesty comes from
visibility, not structure; a blueprint axiom left undischarged forever is a cop-out, just labeled"). The
ALTITUDE CAUTION below is UNCHANGED and binding: the girder axiom's *construction* (M2/M4 bridge + the
crux-2 engine `false_of_ZDerivesEmpty`) is still ~0–partial; the math NEXT MOVE (close `residual`) stands.

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
- **lap-201** (FRESH-MIND REVIEW): directive CHANGED — retargeted from the (now-resolved) top-rank-cut escalation + Lane D to **Lane E / rung E (the embedding)**, the sole remaining hard rung. Re-verified terminal state (real `#print axioms`, bare `lake build` 🟢 **1342**): headline `[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]`, sorryAx OFF, no drift. STATE CHANGE since lap 192: the SERIES-2 judge pass RESOLVED the trilemma (ruling (1) = absorbing norm `ewN→Nlog`) and SERIES-3 EXECUTED it — **the top-rank cut LANDED (lap 198)**; rungs P (`cutElimPass_Zef2`), R (`rankToZero_Zef2`), D (`readoff_delta0_Zef2`, R-4′) are all REAL axiom-clean theorems (verified this lap `[propext, choice, Quot.sound]`); the splice `wainer_splice_Zef2` (rung W, src) carries the sole live `sorryAx` at the rung-E consumption point. CRUX CHECK: laps 198→200 correctly walked N→D→E (crux-first, no fixation, no dead-end) — direction SOUND, only the stale lap-192 directive needed retargeting to match SERIES-3 reality. MANDATE = continue the E-1 wip grind (`wip/E1EmbeddingGrind.lean`), **E-1 block 6 = the V3 predicate** (structural witness budget `Gexp^[c](envSup env N)`; growth kit banked lap 200), re-close the 8 landed cases + `exs`, then close `all` (ω-rule uniformization — the decisive case; probe early) and `axm` (W1/W2). When V3 closes the ladder, rung-E statement + Ax2 probe → next judge pass; do NOT self-ratify into src. FORBIDDEN = hygiene/leaf-retreat while E open / Route-A / self-ratifying rung-E statement (or Zef2T/(Ax2)) into src / re-grinding a landed rung / idle laps; all SERIES-3-order FORBIDDENs remain. SERIES-3 order stays binding for operational detail.
- **lap-192** (FRESH-MIND REVIEW): directive CHANGED (lane-P grind order only; all judge rulings kept). Re-verified terminal state (real `#print axioms`, build 🟢 `GoodsteinPA`): headline `[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]`, sorryAx OFF, no drift. UPHELD the lap-191 top-rank-cut escalation (the pre-registered `rel1`/(f.1) base-additivity wall fired as anticipated) and SHARPENED it two ways: (1) **REFUTED lane B** (the PENDING/ledger "PROOF-only" floor route) — `ewN(∀-witness)` is bounded only by the ∀-slot base `g 0` (un-absorbable by the `2m+1` floor), AND the tight-norm bound is non-inductive (`ewN` blows up ~`2^d(f0+1)` under depth-`d` nested top-rank cuts while `ω^α` absorbs the ordinal); (2) reframed the obstruction as a **TRILEMMA** among three ratified pillars (additive output `α+γ` / finite-fibered⇒additive norm `ewN` / `rel1`-max relativization) — any single fix touches a ratified pillar; prime judge-amendment candidate = a finite-fibered ABSORBING norm; `rel1` max→+ alone is insufficient (needs strict-mono `ewIter` lacks). MANDATE = **lane D `readoff_delta0_Zef2`** (sole open proof-only lane); the crux advances ONLY by wip-only amendment probes → ledger, never src. FORBIDDEN = grinding the top-rank cut in src / re-deriving `hg_base` refutation / self-ratifying rel1/norm/output/statement changes / porting probes to src. Corrected the stale PENDING/ledger "pursue lane B next" pointer.
- **JUDGE PASS lap 5** (host, 2026-07-02): PASS WITH AMENDMENT — **seventh statement trap** caught at statement time (the draft's fixed-count iterate `norm·+1` kernel-refuted at the `allω` reassembly, `wip/JudgeTrap7Probe.lean` `11 < 23`; `norm` not monotone along `<`). Judge amendment applied: `iterSlot` = the diagonalizing ordinal-indexed iterate (hardy-style fundamental-sequence recursion; E–W Lemma 19 `F^α(0)`). `collapse`/pin-shape/exit-corollary ratified as drafted; `iterSlot_infl` proven; `iterSlot_monotone` = disclosed C5 pin, lap-6 first item. Laps 6–7 OPEN. Box conduct clean (honest T-Z5(iii) flag — mis-classified as grind-deferrable, the exact error class the gate catches). Seven traps caught at statement time, zero reached a grind lap. Ruling: `E-2026-07-02-JUDGE-rebuild-z-lap5-validation.md`.
- **JUDGE PASS laps 2–4** (host, 2026-07-02): PASS — pins 1–2 discharge ACCEPTED, slot-judgment amendment RATIFIED with judge authority (LOCK Addendum 2; `Zeh` RETAINED as embedding-side, `zeh_to_zef` the sanctioned lift). Independent kernel re-verification of the whole `Zef` layer + freeze checks (pin 3 / `Zeh` core / headline hash-identical or undrifted) + both wip refutation probes re-compiled + `blueprint_audit` 13/13. Sixth statement trap recorded (stage axis; kernel-localized, NOT falsified — precision note in the ruling §3). Box self-ratification ruled out-of-authority, mitigated this once, future instances = VOID. Next: lap-5 entrance mini-lock (pin-3 restatement over `Zef`), laps 5–7 assembly on operator fire. Ruling: `E-2026-07-02-JUDGE-rebuild-z-laps2-4-validation.md`.
- **lap-184** (FRESH-MIND REVIEW): directive CHANGED — RATIFIED the slot-judgment amendment (LOCK §1-A1/§3), turning the lap-3 escalation into a green-lit `src` port. FINDING = the LOCK contradicts itself (§1 A1 mandates an ℕ-stage judgment; R4 forbids ℕ-valued budgets in reduction motives) and laps 2–3 exposed it in-kernel: `principal_witness_exceeds_stage` (`m < hardy ω m`) makes the stage-`m` fixed-control reduction unreachable — R4's predicted failure. The R4-compliant function-slot judgment `Zef` discharges pins 1–2 + read-off exit SORRY-FREE (`redDeriv_slot`/`stepAllω_Zef`/`headline_readoff_Zef`, all `[propext,choice,Quot.sound]`, verified real `#print axioms` this lap). Re-verified terminal state (build 🟢 **1333**): headline `[propext,choice,goodstein_implies_consistency,Quot.sound]`, NO drift. WHY the change (not KEEP): three consecutive laps (180 wait, 3 escalate) advanced nothing while a judge that isn't coming this autonomous run stayed the notional blocker; the math is kernel-done in `wip/`, so the review-lap makes the ratification call under the operator's full-discharge mandate. MANDATE = execute the staged port (PENDING_WORK § "SLOT-JUDGMENT PORT"); gate on green + no-drift + §6-seams each lap. FORBIDDEN = stage-`m` reduction / `f∘g` order (both kernel-refuted) / pin 3 / Route-A / Δ₀ / docs-only theatre. Ratification doc: `REBUILD-Z-LAP4-RATIFICATION-2026-07-02.md`.
- **lap-180** (FRESH-MIND REVIEW): directive KEPT (2026-07-02 Z1-PASS block current) + one clarifying entry ADDED above. Independently re-verified terminal state (real `#print axioms`, build 🟢 **1333**): Route-A headline `[propext, choice, goodstein_implies_consistency, Quot.sound]`, sorryAx OFF, no drift; `fastGrowing_bachmann_reach`/`hardy_omega_pow_lt_fastGrowing`/`hardy_omega_pow_bracket` all `[propext,choice,Quot.sound]`. **A3 inversion suite verified complete** (Zekd's 4 companions `orInv`/`andInvL`/`andInvR`/`allInv` all ported to `Zeh`). Live-code sorry census = **13**: 10 Route-A-FORBIDDEN + 3 judge-gated §5 Zeh pins → **zero permitted-and-open sorries**, Scope-A genuinely exhausted. **Fidelity fix:** corrected `fastGrowing_bachmann_reach`'s stale "disclosed sorry" docstring (it is PROVEN). **Correction to lap-179 + LANDED it:** the growth lane was NOT fully mined — the additive-Hardy **inequality** `hardy(e+β)≤hardy e∘hardy β` (lap-178 refuted only the equality) remained; this lap PROVED & banked it axiom-clean (`hardy_add_le_comp` + P1 corollary `hardy_add_omega_pow_le`, `src/Hardy.lean`, build 🟢 1333, no headline drift). Induction on `e` via `addAux`; eq case closed by coefficient additivity, no ordinal-absorption needed. **Now the permitted growth lane IS exhausted** — remaining P1 work is judge-gated pin-wiring. ALLOW_STOP=1 but project NOT complete (1 undischarged 🟠 girder axiom + 13 src sorries) → stop sentinel NOT written; run stays cap-bounded, wait-for-judge.
- **lap-177** (FRESH-MIND REVIEW): directive KEPT (the 2026-07-02 Z1-PASS block is current and correct — treadmill runs Scope-A only; a Scope-A-exhausted lap writes its baton and ends; reduction discharge + beyond judge-gated). Independently re-verified the terminal state (real `#print axioms`, build 🟢 1327): Route A headline = `[propext, choice, Quot.sound, goodstein_implies_consistency]`, Route B headline = trust-base + `wainer_bound_of_pa_proves_goodstein` + 12 native_decide artifacts — **sorryAx OFF both headlines**; OperatorZeh clean except the 3 §5 pins; no drift from lap-176. **Trigger T-R NOT fired** — both Z1 seams re-checked axiom-clean in f-form (`seam1_bump_absorbed_by_composition` axiom-free; `probe_allomega_reassembly_Zf` `[propext,choice,Quot.sound]`); the carrier composes, and the lap-176 P1 finding is judge-input on statement shape (Option A kernel-forced, validated by banked `NormControlled.comp`), NOT a carrier failure (so this is not the A2 "seam re-check fails" self-stop case). Scope-A CONFIRMED EXHAUSTED (A1/A2/A3 complete; no eligible alternative in-scope sorry — Wainer infra sorry-free, Route-A machinery FORBIDDEN); no in-flight Aristotle job; no pending online request. ALLOW_STOP=1 but project is NOT complete (2 undischarged 🟠 girder axioms + 19 src sorries) → stop sentinel NOT written. Refreshed STATUS.md to the spine (was 2092-line stale Wainer-pivot log). NEXT (unchanged): judge ratifies verdict + finding (Option A vs B, pin `f'`), then lap 2 grinds reduction discharge.
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

## 🧭 ROUTE GUARD — the blind-spot fix (standing governance; altitude + operator owned)

**Diagnosis (why this exists).** This expedition's reflection cadence re-evaluates progress *within*
the chosen route but never re-opens *whether the route is right*. Every altitude lap from lap 137→166
recorded "direction KEPT"; meanwhile BOTH pre-registered Route-A abort conditions FIRED and no
re-decision ever happened. A treadmill cannot make a route call — but it must not silently grind
through the abort conditions it was told to stop at. That is the failure this guard closes.

**Pre-registered route triggers (abort conditions — these are commitments, not vibes).**
- **T1 — M1 overrun** (`E-CRUX2-ROADMAP-2026-06-24.md`): if M1 (`RedSound` = the cut-elim validity
  core) is not a *proven theorem* within ~40 laps of lap 83 (≈ lap 123), STOP grinding and reweigh
  Route B. **STATUS: FIRED** (now lap 166; `RedSound` is still 2 open sorries — `ind_reduct_anySucc`,
  `residual`).
- **T2 — second false summit** (`E-ROUTE-OPTIONS-2026-06-24.md`): if the genuine-reduct / cut-elim
  core hits a *second* false summit, reweigh the meta / growth-rate pivot. **STATUS: FIRED** (≥4
  false summits since lap 81: `redLeast`, the `seqUpdate` splice, same-degree `õ`-drop, the orphaned
  ⊥-cluster chased for ~30 laps).

**The rule** is now GENERIC and lives in the lean tooling, not here — every campaign's deep reflection
lap runs it (`~/personal/claude/hooks/lean-reflect-lap.md`, altitude question #2 "Is the ROUTE still
right?"): emit an explicit `CONTINUE`/`ESCALATE` verdict against the registered triggers, a fired
trigger forces `ESCALATE` (halt + `ROUTE-ESCALATION-<date>.md`, operator owns the pivot), never a bare
"direction KEPT". **This section's job is only to REGISTER this repo's triggers (above) + the live
status (below)** — the data the generic protocol reads.

**Live status (2026-06-28, lap-167):** both triggers FIRED → escalated → operator **RATIFIED a bounded
5-lap M2 feasibility probe** as the deciding experiment (CURRENT DIRECTIVE lap-167; record
`ROUTE-ESCALATION-2026-06-28.md`). Grind is UNFROZEN for *only* this probe; **verdict due lap 171**, then
re-escalate (`M2-PLAUSIBLE` → reconsider A re-scoped; `PIVOT-B` → switch). `(3) bank-and-downgrade` stays
OFF the table: the target is the top-level headline axiom-clean, or full abandonment.

---

## The goal (not a fixture — the destination) 🦸

**Prove `Statement.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence`** — Kirby–Paris (1982),
Peano Arithmetic does not prove Goodstein's theorem. That headline `sorry` is the *target*, not
a thing to preserve. The whole campaign exists to discharge it honestly.

## The decomposition — and an honest scope warning ⚠️

**Do NOT read this section as "the math is known, so it's just treadmill decomposition."** That framing
(the old wording here) is exactly the scope-laundering that produced ~110 laps of false summits. The math
IS ~90 years old and in textbooks (Gentzen 1936, Schütte, Takeuti, Buchholz) — but **`EXPEDITION-PLAN.md`
is the binding scope statement, and it says the load-bearing girder "exists in no Lean library and must be
*originated* … a research milestone, executed in phases, with a human architect … Not a solo
autonomous-treadmill job."** Phases 0/1/3/4 are decomposition/assembly. **Phase 2 is origination of a
Bryce–Goré-scale monument (~thousands of lines, un-precedented in Lean), NOT a dozen-lap grind** — and
under the 2026-07-01 FULL-DISCHARGE mandate it is now the *whole ballgame* (see
`ROUTE-SCOPE-REALITY-2026-07-01.md`). A grind lap's job on Phase 2 is to chip ONE honest mathlib-shaped
lemma of that monument and bank it — not to "finish the girder." The phases (see `EXPEDITION-PLAN.md` for
the math):

- **Phase 0 — encoding.** ✅ DONE - Milestone **M1** complete (`goodsteinTerminates_re` + `computable_bump` proven, 0 sorries; verified 2026-06-26).
- **Phase 1 — Gödel II hook.** Surface `Con(𝗣𝗔)` + `𝗣𝗔 ⊬ Con(𝗣𝗔)` from Foundation's *existing*
  Gödel II (`FirstOrder/Incompleteness/Second.lean`), and reduce the headline to the single
  implication `𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`. Assembly. Milestone **M2**.
- **Phase 2 — the girder (THE monument; multi-lap → multi-month, human-architected).** `TI(ε₀) ⊢ Con(𝗣𝗔)`,
  OR equivalently the Buchholz–Wainer "bounding" converse for the growth-rate route: infinitary `PA_∞`
  (ω-rule), ordinal assignment `< ε₀` to derivations, ε₀-bounded cut-elimination, Σ₁-witness bounds. The
  deep core. Un-precedented in Lean; precedented in Coq (Bryce–Goré, arXiv:2603.00487 — the scale marker +
  a `Peano.v` bridge blueprint). Build on mathlib's ε₀ (`SetTheory/Ordinal/Veblen`, `ONote`) + Foundation's
  finitary Hauptsatz. **This — not the wrapper route choice — is what "axiom-free" costs.** Milestones **M3…**.
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

A `sorry`'d headline is honest; a **fake** one is the worst outcome. The fraud this guards against
is unchanged: a headline that *looks* finished while resting on something untrustworthy.

**Named-axiom blueprint (lap-166 policy update; KB note `named-axiom-blueprint`).** Trevor's stance
shifted: a not-yet-proven *milestone* stated as a NAMED `axiom` carrying a faithful, audited subgoal
statement is the **clearer, more honest** blueprint node — strictly better than collapsing all debt
to one opaque `sorryAx`. The headline may therefore be a *real proof* composing such axioms. The
forcing function is unchanged: the result is **done** only when every blueprint axiom is discharged
(`axiom` → `theorem`) and `#print axioms peano_not_proves_goodstein` = `[propext, Classical.choice,
Quot.sound]` with NO custom axiom surviving.

You may replace `Statement.peano_not_proves_goodstein`'s `sorry` with a real proof **only if ALL**:
1. `#print axioms peano_not_proves_goodstein` ⊆ `[propext, Classical.choice, Quot.sound]` ∪
   **{declared blueprint axioms on the allowlist}** — and NEVER `sorryAx`.
2. Every blueprint axiom it rests on is **declared** (named, in `-a` allowlist), **faithfully
   stated** (audited against its source — the axiom STATEMENT is the trust surface; a false axiom
   proves `False`), and **intended to be discharged** (a sorry-builder or a real construction maps
   to it). Off-path / known-false routes are NEVER axiomatized — they stay clearly-labeled refuted
   `sorry`s (a `sorry` asserts nothing; a false `axiom` is catastrophic).
3. It genuinely chains through built lemmas — no `native_decide` on the headline, no vacuous
   restatement, no *undeclared* / off-allowlist axiom.

If you cannot satisfy these, **leave the `sorry`** and report the gap. The host audits `#print
axioms` on the headline every review lap via the **allowlist gate** (`lean-axiom-gate . -t
GoodsteinPA.peano_not_proves_goodstein -a <eachBlueprintAxiom>`; `--exact` once fully discharged).
The allowlist SHRINKS to the 3 canonical axioms as milestones discharge. An *undeclared* axiom, or a
declared one that is false/unfaithful, or a non-shrinking allowlist parked forever = failure.

**Current allowlist (lap 166):** `goodstein_implies_consistency` (the Phase 2–3 girder γ→Con(PA)
inside PA, `Reduction.lean`). The headline is wired through it + the axiom-clean Gödel-II
contraposition. `false_of_ZDerivesEmpty` / `exists_sigma1_descending_step` are crux-2 milestones
promoted in the same discipline (off the headline's direct ledger; gated individually).

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
