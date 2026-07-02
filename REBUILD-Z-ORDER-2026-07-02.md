# REBUILD-Z — the `Zᵉ` calculus rebuild (operator-fired treadmill order, 2026-07-02)

> **Status: READY — awaiting the operator to fire.** Gate satisfied: judge-ratified Z1 PASS
> (`E-2026-07-02-JUDGE-spike-z1-validation.md`). Binding companions, read BEFORE lap 1:
> `ZEH-STATEMENT-LOCK-2026-07-02.md` (the locked forms + rails — outranks this order),
> `SPIKE-Z1-VERDICT.md` (amendments A1/A2, K1–K3, the §6 function-slot form),
> `DIRECTION.md` (mandate: full discharge or abandon; the fork green-light block).
> Estimate: **~7–11 laps** (calibration envelope ~7–20). Pre-registered trigger **T-R**
> (below) returns to the operator with the abandon branch live.

## Objective

Rebuild the operator cut-elimination engine on `Zeh` (the someK/Wainer-debt discharge
substrate) far enough that the composed chain

```
PA ⊢ goodsteinSentence  →  Zeh embedding  →  cut-elimination  →  headline_readoff
                        →  witness ≤ hardy e m  →  contradict goodsteinLength growth
```

has every calculus-side link either proven or reduced to the named W-ladder leaves. This
order covers the CALCULUS (the W4/W4B-scoped work re-keyed to `Zeh`); the embedding (M4/W3
side) and final assembly stay on the masterplan's ladder and are NOT this order's scope.

## Lap plan

- **Lap 1 — STATEMENT LAP (no grinding; ends at a mini-verdict).** In
  `src/GoodsteinPA/OperatorZeh.lean`: seed §0–§2 + `mono_H` + `ZehProv` + the read-off block
  from `wip/SpikeZ1Seams.lean` VERBATIM (LOCK §1). Then draft — statements only, bodies
  `sorry` — the f-slot elimination suite per LOCK §3: the running-family reduction
  (`cutReduceAllAuxRunning_Zf`-class), the common-control step motive (A2 form), and the
  collapse/iteration shape, each with its f-slot composed at principal cuts and
  max-relativized (`rel1`) at ω-nodes, `hardy e` at the root. Kernel-check the two Z1 seams
  RE-EXPRESSED in the f-form (the Z1 probes re-run against the new statements — real proofs,
  pins consumed, no sorried memberships/slots). Write `REBUILD-Z-LAP1-VERDICT.md`; **STOP for
  the judge.** Laps 2+ are gated on that judge pass (statement traps have been caught at
  statement time four times running; this is the cheapest place to catch the fifth).
- **Laps 2–4 — inversion suite + reduction discharge.** Port `allInv` → `allInv_Zeh` (pin 1;
  mirrors the banked `OperatorZinfty.lean:484` induction), the companion inversions the
  banked suite carries, then discharge the lap-1 reduction statements. Expect the
  hardy-domination question (LOCK P1) to surface here — a kernel-confirmed obstruction on the
  threading design is a FINDING: switch to the pre-validated BW87 fallback (cut-free
  read-off), do not grind against it.
- **Laps 5–7 — cut-elimination assembly.** Rank lowering + the elimination pass at the
  once-per-pass raised control; per-instance hardy-domination discharged at the headline
  shape (or f-slot carriage throughout, whichever lap 1 pinned). Deliverable: rank-`c` →
  rank-0 at towered ordinal/control, kernel-clean.
- **Laps 8–10 — the Δ₀ read-off extension (LOCK P2/J3).** Extend `readoff_sigma1` to
  bounded-∀ matrices (Towsner-5.4 pattern, `prwoInstance` discipline) so the exit consumes
  the actual Goodstein-sentence matrix. This is scheduled work — budget it, don't discover it.
- **Lap 11 — integration audit.** `#print axioms` sweep of the full chain's calculus links;
  reconcile the blueprint ledger; a REFLECTION doc mapping what remains on the W-ladder
  (embedding + assembly) with fresh estimates.

## Overnight / treadmill scope — **Scope-A** (what runs WITHOUT the lap-1 judge pass)

A treadmill fired against this order executes **Scope-A only**, then self-stops:

- **(A1)** Seed `src/GoodsteinPA/OperatorZeh.lean` verbatim per LOCK §1 (mechanical; the
  statements are judge-ratified). Repo stays green.
- **(A2)** The lap-1 statement work: draft the f-slot elimination statements (bodies `sorry`)
  and kernel-re-check the two Z1 seams in f-form; write `REBUILD-Z-LAP1-VERDICT.md`. If a
  seam re-check fails in f-form, that is T-R(i) territory: write the finding, self-stop —
  do NOT grind against it.
- **(A3)** The inversion-suite grind: discharge `allInv_Zeh` (pin 1) + the companion
  inversions mirroring the banked, PROVEN `Zekd` suite. Their statements were audited in the
  Z1 judge pass and do not consume the f-slot statements — safe grind regardless of how A2
  lands. Park hard cases with named blockers rather than forcing them.
- **SELF-STOP when Scope-A is exhausted** (A2's verdict written + A3 discharged-or-parked).
  Everything else — reduction discharge, cut-elimination, the Δ₀ read-off extension — is
  **judge-gated behind the lap-1 verdict** and FORBIDDEN until the judge ratifies it.

## Session rules (per lap)

Treadmill grind rules as standing (DIRECTION.md) plus:

- Work sites: `src/GoodsteinPA/OperatorZeh.lean` + `wip/` probes. `wip/SpikeW4*.lean` /
  `wip/SpikeZ1Seams.lean` are **evidence artifacts — read-only**. No `(k,d)`-motive work of
  any kind.
- Every lap ends green (`lake build`), commits, and writes its baton
  (`HANDOFF-2026-07-02-lapN.md` scheme continues). No new `axiom` declarations; sorries only
  as statement pins with a named discharging lap; `#print axioms` on every completed theorem
  in the lap notes.
- The LOCK outranks this order; this order outranks lap momentum. A lap that believes a
  locked form is wrong STOPS and escalates.

## Pre-registered trigger T-R (fires to the operator, abandon live)

T-R fires if **either**: (i) the f-slot reduction statements cannot be kernel-composed at the
two Z1 seams by the end of lap 2 (i.e. the E–W carrier itself fails where the ℕ-slots
failed — no third carrier is pinned), or (ii) BOTH threading designs die — per-instance
hardy-domination kernel-refuted at the headline shape AND the BW87 cut-free fallback fails to
emit legal `Zeh` (P1's residual) — with the failure kernel-confirmed, not estimated. Either
way: verdict-style writeup, STOP, operator decides. `Zᵉ` was the last pre-named fallback.

## What PASS looks like (end of this order)

The calculus chain proven: embedding-input interface stated, cut-elimination to rank 0 at
towered control, read-off consuming the actual headline matrix — with
`wainer_bound_of_pa_proves_goodstein`'s discharge reduced to the W-ladder's embedding lap
plus assembly arithmetic. Zero new axioms, blessed `native_decide` base only.
