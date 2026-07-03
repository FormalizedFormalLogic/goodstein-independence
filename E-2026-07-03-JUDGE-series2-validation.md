# JUDGE RULING — REBUILD-Z SERIES-2 pipeline validation + the two amendment rulings (2026-07-03)

**Scope**: SERIES-2, commits `07d0dd8..1fc0aef` (13 commits on `plan`), executed under
`REBUILD-Z-SERIES-2-ORDER-2026-07-03.md`. All gates judge-rerun. Ran on a different model
(Fable 5, low effort) from lap 197 — noted because the gates are model-agnostic by design, and
they held.

## VERDICT: **SERIES PASS** ✅ (one omission defect, §4)

## 1. Mechanical gates (judge-rerun, HEAD `1fc0aef`)

| Gate | Result |
|---|---|
| bare `lake build` | 🟢 (1342 jobs — +1 for `WainerLadder.lean`, as expected) |
| Headline | `[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]` UNDRIFTED, sorryAx OFF |
| Freeze (`wip/EwIter.lean`, `wip/Zef2Calculus.lean`, `src/.../OperatorZeh.lean`) | **0-line diff** — untouched |
| Stage-A deletions **verified by diff** | `embedding_Zef2` GONE, old parametric `wainer_splice_Zef2` GONE (the Series-1 false-ledger lesson, applied) |
| A-2 restatement | **verbatim** vs the order block; homed in `WainerLadder.lean`, wired; sweep = `[propext, sorryAx, Classical.choice, Quot.sound]` as expected |
| src purity | no `Nlog`, no `trueRel`/`trueNrel` outside pre-existing `Zekd`; no src grind on the reserved cruxes |
| `lean-sorry src/` | **17** exactly (Crux2 ×12 frozen, DescentSemantic 1, OperatorZeh 1, OperatorZef2 2 = top-rank + trapped, WainerLadder 1 = restated splice) |
| Probes (all 5: AbsorbingNorm, Ax2Adequacy, GuardMono, OptionBSplice, Rel1Shift) | judge-recompiled **clean** |
| `blueprint_audit` | PASSES (16 nodes) |
| New axiom / native_decide | 0 / 0 |

## 2. Stage ratifications

- **A** ✅ (mechanical debt cleared; Series-1's R-5/R-6 defect closed).
- **D-1** ✅ — `Nlog_add_le_max_succ` (absorption) + `Nlog_finite_fiber` (NF fibers) both proven,
  standard triple; the unrestricted fiber statement kernel-REFUTED (`Nlog_fiber_infinite_without_NF`,
  non-NF flat chains) and correctly restricted to NF — the only population the calculus feeds.
  The lap-192 "finite fibers force additivity" conjecture is REFUTED. **RATIFIED.**
- **C-1** ✅ — Option-B exit bound is the (d+1)-tower **by `rfl`**; splice-side structurally free.
  **RATIFIED.**
- **C-2** ✅ — `guardShape_not_mono`: the goodstein bounded-∀ guarded-implication shape defeats the
  mono guard. This **kernel-corrects the lap-195 claim** (echoed in my Series-1 ruling §3) that
  `readoffD_trapped_of_mono` covers Goodstein's clauses — it does not; the brick stays ratified as
  a theorem, its headline-path applicability is dead. On the record. **RATIFIED.**
- **B (B-1)** ✅ — `Zef2T` answers all three: (i) strict rank-0 extension, `toZef` route breaks
  (read-offs need native re-proof under adoption); (ii) reduction extends mechanically;
  (iii) read-off falsity invariants treat (Ax2) leaves vacuously — its value is embedding-side
  derivation existence. **RATIFIED.**
- **D-2** ✅ — `rel1'` preserves EwLow but NOT `hg_base` (kit-satisfying counterexample);
  `StepAdd` is the shift-stable upgrade class and the concrete root slot has it; blast radius
  measured (allω BINDS `rel1` structurally → new inductive + full-suite re-proof).
  **Verdict ratified: shift package viable but strictly dominated by D-1.**

## 3. THE TWO RULINGS (on the evidence above)

### Ruling (1) — top-rank cut: **the absorbing-norm route (`ewN → Nlog`) is RATIFIED AS PRIME**,
conditional on one entry gate.

The judge's independent check found the one open obligation D-1's package does not yet discharge:
`absorbing_closes_gate` requires `hslack : max (g 0) (f 0) + c ≤ g (f 0)`, and at the cut node
(`g = ewIter s βφ`, `f = ewIter s βψ`) this is **not free** — the `βψ = 0` edge gives `f 0 = 0`
and hslack degenerates to `g 0 + c ≤ g 0` (false); plateau slots stress it the same way `hg_base`
died. Therefore:

- **T-S3 entry gate (HARD, wip, before any src swap)**: kernel-discharge hslack for the actual
  cut-node slots from the threaded kit (Monotone + infl + EwLow + node gates), INCLUDING the
  ordinal edges `βφ, βψ ∈ {0, 1}` — or characterize the failing edges and prove the case-split
  plan that dodges them (e.g. a `βψ = 0` premise handled by direct weakening, no reduction
  needed). Also required: the `Nlog` analogs of `ewN_collapse`/`ewN_collapse_le` (the per-node
  and Def-16 iterate gates).
- On T-S3 passing: the swap executes **in place** on `Zef2` (the gate norm becomes `Nlog`;
  no constructor shape change, `rel1` and the `α+γ` output untouched). Every ratified statement's
  text under the **deterministic substitution `ewN → Nlog`** is pre-ratified
  verbatim-by-construction (zero authoring freedom — copy-not-compose is preserved). The proof
  suite re-grinds on the Series-1 templates; `Nlog` + its two theorems promote from the probe
  to src as load-bearing content.
- The shift package {`rel1'`, `StepAdd`} is **ratified as the fallback** if T-S3 fails on the
  absorbing route (it dodges hslack differently), at its measured new-inductive cost.

### Ruling (2) — lane-D residue: **the R-4′ restatement is RATIFIED**; (Ax2) is deferred to rung E.

R-4′ verbatim text (sole change: the conclusion bound; everything else byte-identical to the
ratified R-4):

```lean
theorem readoff_delta0_Zef2 {φ : SyntacticSemiformula ℒₒᵣ 1}
    (hφbdd : ∀ n, LO.FirstOrder.Arithmetic.DeltaZero (φ/[nm n]))
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
    (dd : Zef2 α e H f 0 {(∃⁰ φ)}) :
    ∃ n ≤ ewIter f α 0, atomTrue (φ/[nm n])
```

Grounds: C-2 proves the amendment is load-bearing (no mono rescue on the concrete matrix); the
lap-195 algebra shows `ewIter f α 0` is the structurally achievable bound; C-1 proves the splice
consumes it at one definitional tower level. **(Ax2)/`Zef2T` adoption is NOT ruled now** — it is
exactly rung E's faithfulness question (B(iii)), decided at the rung-E statement work on a
kernel probe of whether the embedding's true-Δ₀/PA-axiom leaves require true-literal closure.
B's cost measurements (read-offs native re-proof; reduction mechanical) stand ready either way.

## 4. Defects

1. **B-2 (rung-E statement draft) silently skipped** — no draft, no reasoned-deferral note in
   ledger or baton. Defensible on the merits (B(iii) makes the draft depend on the Ax2-need
   probe), but the order asked for the text and the ledger owed the deferral one line. Same
   omission class as Series-1's R-5/R-6, smaller. Rolled into Series-3 Lane E as its first item.
2. Minor: the lap-196 blueprint edit dropped `\notready` on rung R per my A-4 instruction, which
   conflicts with the tex's own discipline header (rung R still carries sorryAx through the
   pass). My defect, not the run's — Series-3 restores `\notready` on rung R until the pass
   lands (the prose already carries the "flips automatically" nuance).

## 5. Commendations

Six stages closed in ~2 laps across a mid-series model swap; two false statements caught and
kernel-refuted instead of proven-around (the non-NF fiber ball; the mono-guard coverage — the
latter correcting the *judge's own* echoed claim); every probe answer arrived with its negative
space measured (costs, blast radii, honest limits). The evidence packages made both rulings
essentially mechanical. The trap ledger's discipline (statements verbatim, probes kernel-first)
has now survived three series, two models, and two effort tiers.

## 6. Orders

Series-3 order issued: `REBUILD-Z-SERIES-3-ORDER-2026-07-03.md` — the post-ruling GRIND series
(all four lanes, ladder + high stop bar, sized for a long run). STATUS + blueprint touched by
this pass.

— series judge, 2026-07-03
