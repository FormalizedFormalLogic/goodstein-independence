# REBUILD-Z — LAP-7 ENTRANCE ORDER: the E–W rebuild of the slot calculus (architect, 2026-07-02) 🔒

> **Binding.** Written by the judge/architect pass that ratified the laps-6–7 run and the EIGHTH
> statement trap (`E-2026-07-02-JUDGE-rebuild-z-laps6-7-validation.md`). Companions: the trap-8
> escalation (`REBUILD-Z-TRAP8-2026-07-02.md` + `wip/Trap8Probe.lean`) and the judge's fork-closing
> probe (`wip/JudgeTrap8FixProbe.lean`). Grind laps work strictly within this; a lap that believes
> a locked form here is wrong STOPS and escalates — **self-ratification is VOID** regardless of
> evidence quality. **This lap touches NOTHING under `src/` — wip-only.**

## 1. The ruling this order executes

Trap 8 killed the `(fs-recursion iterSlot, bare Zef)` C2 shape. The fix is **Eguchi–Weiermann
taken literally** (arXiv:1205.2879, PDF in `papers/` — read pp. 8–12 yourself; the `.md` summary
is a pointer, not a substitute). Three coupled elements, ratified as one design:

- **(E1) The iterate becomes the norm-gated MAX** (Def 16), fundamental-sequence-FREE:
  `ewIter f 0 = f`; for `0 < α`,
  `ewIter f α m = max{ ewIter f β (ewIter f β m) | β < α, norm β ≤ f (norm α + m) }`.
  It dominates every gate-admissible `ewIter f β` by construction (Cor 17.2) — this is what
  replaces the dip-prone fs-recursion (`wip/JudgeTrap8FixProbe.lean` kernel-proves the fs-form
  dips even on admissible instances).
- **(E2) The judgment carries the norm side condition** (Def 23's HYP, PA-shadow): every node of
  the new judgment `Zef2` requires `norm α ≤ f 0`. Consequence (the trap-8 killer): every
  sub-derivation ordinal β has `norm β ≤ f 0 ≤ f (norm α + x)` for ALL `x`, so the gate holds
  everywhere and the pointwise lift `ewIter f β ≤ ewIter f α` is UNCONDITIONAL on admissible
  sub-derivations. The sharp impossibility (`no_fixed_arg_monotone_unbounded_slot`) dissolves:
  monotonicity is only needed on the norm-bounded admissible family, never against unboundedness.
- **(E3) Witness reads stay at argument 0.** Def 23's (⋁) reads `N(ι₀) ≤ f(0)`. `exI`'s
  `n ≤ f 0` was never the defect; the trap-8 doc's §8 "relativize the exI read" direction is
  SUPERSEDED. `allω`'s `rel1 f n` branch relativization matches (⋀)'s `f[N(ι)]` and stays.

## 2. Locked constraints (Z1–Z7)

- **(Z1) `collapse := expTower` unchanged** (ratified at lap 5; the ordinal side of the pass is
  not in question).
- **(Z2) `ewIter` per Def 16, verified against the PDF** — Def 16 + Cor 17 + Lemma 19 (norm
  bound), Lemma 20/21 + Cor 22 (the flattening arithmetic; the paper's own caveat: this is where
  the side-condition sweat lives, pp. 14–17 for downstream use). Base case `ewIter f 0 = f`
  matches the retired `iterSlot`'s. Note the max is over a NONEMPTY set for `α > 0` (β = 0 always
  gate-passes).
- **(Z3) Implementability of the gated max is a DELIVERABLE, not an assumption.** The max needs
  `{β | β < α ∧ norm β ≤ K}` finite (and preferably listable). FIRST verify the repo's `norm`
  has finite fibers (`{β : ONote | norm β ≤ K}` finite — check the actual `norm` definition in
  `Hardy.lean`; if its fibers are infinite, adopt E–W's `N` verbatim as a new def — Def 13.3:
  every constructor strictly increments — and gate on that instead). A noncomputable realization
  (`Set.Finite.toFinset` + `Finset.max'`, or `sSup` on ℕ) is ACCEPTABLE — the pass only ever
  reasons through the defining equations; value anchors may be proven from the defining equations
  on small instances instead of `native_decide` if computability is lost.
- **(Z4) The slot hypotheses become E–W's `(f.1)/(f.2)`** (p. 8): `(f.1)` f strictly increasing
  with `2m+1 ≤ f m` (subsumes `Monotone` + inflationary; gives `n + f m ≤ f (n+m)`); `(f.2)`
  `2·f m ≤ f (f m)`. These are load-bearing in every norm computation. **C3-exit check at
  statement level**: the canonical root slot `rel1 (hardy e) m` must be shown to satisfy
  (f.1)/(f.2), or — E–W's own sanctioned move — the exit instantiation composes with a fixed base
  (`s^ω`-class) that does. Kernel-check whichever route at statement level; a silent hypothesis
  the exit can't meet is severed-slot vacuity in new clothes.
- **(Z5) The judgment `Zef2`** (new inductive, defined in wip ALONGSIDE the frozen `Zef` — src
  untouched): `Zef` plus, per Def 23's PA-shadow: (i) the HYP clause `norm α ≤ f 0` carried at
  every constructor (pattern: alongside the existing `hαNF`); (ii) rule-local norm clauses ONLY
  where Def 23 has them after the F-side (`K_Ω`, `ord(ι)`, `Cl_Ω`) is deleted — decide each with
  the paper open, do not guess; expected shape: (⋁)/`exI` keeps `n ≤ f 0` (that IS `N(ι₀) ≤ f(0)`
  for numerals, `N = val`); (Cut) gains the `lh(C) ≤ f 0`-shadow (Lemma 25's proof consumes it);
  (⋀)/`allω` branch stays `rel1 f n` (= `f[N(ι)]`). Keep `e` phantom; height/rank plumbing
  (`c`, `Γ`, `wk`/`weak`) unchanged.
- **(Z6) The pass restatement (wip, body `sorry`)**:
  `Zef2 α e H f (c+1) Γ → (f.1) → (f.2) → Zef2Prov (collapse α) e H (ewIter f α) c Γ`,
  with `Zef2Prov` the height-only-slack wrapper (R2 unchanged: existentials root-only). The
  composed C3 exit corollary must typecheck with the `ewIter … 0` bound VISIBLE and consumed by
  the read-off (restated against `Zef2`'s read-off port in wip).
- **(Z7) MANDATORY kernel pre-probes, in wip, BEFORE the restatement is drafted** (the
  anti-trap-9 gate — each is a real sorry-free theorem or the lap STOPS):
  - **(P1) The lift**: `β < α → norm β ≤ f 0 → (f.1) → ∀ x, ewIter f β x ≤ ewIter f α x`.
    This is the exact proposition trap 8 refuted for `iterSlot`; if it fails for `ewIter` the
    ruling itself is wrong (trap 9) — escalate immediately with the kernel instance.
  - **(P2) The trap-8 instance re-run**: at an admissible `f` (e.g. `·+2`), `β = ofNat 2`,
    `α = ω`: show the lift HOLDS for `ewIter` (values via the defining equation or the P1
    theorem) — the direct kill-confirmation of the dip.
  - **(P3) The trap-7 instance re-run**: the `allω` reassembly containment shape
    (`ewIter (rel1 f n) (β n) ≤ rel1 (ewIter f α) n`-class, at the `11 < 23` instance's
    parameters) — sanity that the gate's `m`-widening pays the branch growth the fixed count
    could not. A wall here is T-Z7(iii) territory, not a reason to improvise.
  - **(P4) The embedding seam, statement-level plan only**: where do `zeh_to_zef2`'s per-node
    `norm α ≤ f 0` obligations come from? E–W sources them at the leaves via the
    f-relativization (Lemmas 32–34: formula/term norms enter `f[n]`). Identify the recipe for
    the repo's `Zeh` trees (control tower `e`, root slot `rel1 (hardy e) m`) and name it — a
    disclosed pin with a named lap is acceptable (LOCK R5); a hand-wave is not.

## 3. Lap plan

- **Lap 7 — STATEMENT LAP, WIP-ONLY (no grinding; ends at a verdict; STOP for the judge).**
  (a) Z3 finiteness/implementability of the gated max (+ norm-fiber check). (b) Define `ewIter`
  (Z2) + prove Cor-17-class basics (strict-increase, inflationarity, the P1 lift). (c) Run
  probes P1–P3; write up P4. (d) Define `Zef2` (Z5) + port `mono_f`/`change_H`-class plumbing
  far enough to state the pass. (e) Restate pin 3 + the composed exit per Z6 (bodies `sorry`),
  kernel-check the C3 consumption at statement level. (f) Write `REBUILD-Z-LAP7-VERDICT.md`;
  **STOP for the judge.** Everything in `wip/` (suggested: `wip/EwIter.lean`,
  `wip/Zef2Calculus.lean`); `src/` diff must be EMPTY.
- **Lap 8 — the judged src port** (only after the lap-7 judge pass): `Zef2` + `ewIter` into src,
  re-prove pins 1–2 + inversion suite + `zeh_to_zef2` + read-off on the amended judgment,
  retire/re-pin pin 3 in the new form. (Precedent: the lap-184 wip → laps-2–4 judged-port
  pattern.) **Also erects the wainer ladder** — the named pin chain E/P/R/D/W/C decomposing the
  `wainer_axiom` discharge, with per-rung ledger attributes (`WAINER-LADDER-2026-07-02.md`).
- **Laps 9+ — the pass grind** on the ratified `Zef2` form (estimate re-based at the lap-7
  verdict; the Lemma-20/21/Cor-22 flattening arithmetic is the expected long pole).

## 4. Pre-registered triggers (hitting one is a finding, not a failure)

- **T-Z7(i)**: the repo `norm` lacks finite fibers AND E–W's `N` (Def 13.3) also fails to give a
  listable gate on ONote → architect. Do not weaken the gate to recover computability.
- **T-Z7(ii)**: probe P1 (the lift) is kernel-refuted for `ewIter` → the ruling's mechanism is
  wrong (trap 9); escalate with the instance. Nothing downstream of it may proceed.
- **T-Z7(iii)**: probe P3 (allω reassembly) is kernel-obstructed → the gate's growth is
  insufficient at limit reassembly; architect-level (possibly the Lemma 21/Cor 22 relativized
  forms are the missing carriers — cite the exact page if so).
- **T-Z7(iv)**: P4 has no finite recipe (Zeh-tree norms not boundable by the root slot) →
  architect; E–W's Lemma 33/34 height-indexed relativization is the fallback pattern to cite.

## 5. FORBIDDEN (unchanged + new)

`src/` untouched ENTIRELY this lap (statement work lives in wip; the port is lap 8, judge-gated).
Pins 1–2, `Zeh` core, `Zef` + `zeh_to_zef`, read-off, `iterSlot`/`collapse` + the §5b lemmas:
frozen (hash-checked). NO fs-recursion revival for the iterate; NO fixed-count iterate; NO
argument-0 fixed-read slot maps (all three kernel-refuted — `wip/JudgeTrap7Probe.lean`,
`wip/Trap8Probe.lean`, `wip/JudgeTrap8FixProbe.lean`). Route-A, Δ₀ extension, `(k,d)` work
untouched. `wip/*Probe.lean` evidence artifacts read-only. No self-ratification (VOID).

## 6. Treadmill shape (operator fires; sized to the permitted scope)

- Lap 7 alone: `--max-laps 1` (statement lap + verdict, then STOP for the judge — a second lap
  has nothing permitted to do).
- **Estimates** (calibration: statement/judge cadence 1-session-accurate; grind 2–4× optimistic):
  lap 7 = 1 session; lap 8 port = 1–2 sessions; pass grind = re-based at the lap-7 verdict.
