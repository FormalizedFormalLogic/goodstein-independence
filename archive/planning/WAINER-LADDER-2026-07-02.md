# WAINER LADDER — decomposing the `wainer_axiom` discharge (architect, 2026-07-02)

> **Status: architect sketch, NOT ratified statements.** Operator ask (2026-07-02): break the
> monolithic `wainer_axiom` ledger node (30–60 laps @ 60%) into intermediate lemmas so progress
> is measurable and risk is factored. Every rung below enters through the SAME statement-lap +
> judge gate as everything else — eight statement traps say architect-sketched statements are
> shapes, not truths. **Erected at lap 8** (the judged `Zef2` port), not before: every rung
> quantifies over the judgment, and `Zef2` replaces `Zef` at that port — stating them earlier
> writes statements the port invalidates.

## What green costs (the target, exactly)

`routeB_headline` (`peano_not_proves_goodstein_growth`, ledger 15) is non-clean on exactly:
`wainer_bound_of_pa_proves_goodstein` (ledger 14, the monolith this ladder replaces) + the 12
`goodsteinLength_base_cases` native_decide axioms (masterplan W7 burndown — bounded, mechanical,
separate). Ladder discharged + W7 burned ⟹ headline green (its own wiring: 1–2 laps @ 90%).

## The rungs (E–W pipeline order; per-rung ledger attributes at lap 8)

- **P — the pass** (pin 3, `cutElimPass` on `Zef2`; E–W Lemma 30 shadow). IN FLIGHT — the
  lap-7 entrance order (`REBUILD-Z-LAP7-ENTRANCE-2026-07-02.md`) is this rung's critical path.
  All eight statement traps cluster here; it is the concentrated-risk girder. Est. 4–7 sessions
  total (incl. the lap-8 port) @ ~70%, contingent on probe P1 (the lift).
- **R — rank-to-0** (predicative elimination shadow, E–W Lemma 27's PA-fragment): iterate P
  down the cut-rank `d → 0`; ordinal tower `expTower^[d]`, slot tower `ewIter`-composed.
  A plain induction over P. Est. 1 lap @ 90%.
- **D — Δ₀ read-off extension**: `headline_readoff` (proven, atomic matrices) → the goodstein
  sentence's bounded-∀ matrix (Towsner-5.4 pattern; the old laps-8–10 target
  `readoff_sigma1_Zef` re-homed to `Zef2`). Independent of P once `Zef2` stabilizes.
  Est. 2–3 laps @ 80%.
- **E — the embedding** (E–W Lemmas 32–36 shadow): `𝗣𝗔 ⊢ ↑goodsteinSentence` ⟹ a controlled
  `Zef2` derivation of the translation (tower `e`, root slot, cut-rank `d`, **and the new
  per-node norm side conditions** — the lap-7 P4 seam plan feeds this; E–W source the bounds
  at the leaves via the f-relativization, Lemmas 32/34). The W3 spike (`83e4bca`, judge-ratified)
  already fixed the statement SHAPE (Towsner-§16 K-hypothesis form) — rebase onto `Zef2`, do
  not re-derive. **The long pole after P.** Est. 8–20 laps @ 65%.
- **W — the splice**: compose E → R → D; convert the exit bound to the axiom's
  hardy/fastGrowing vocabulary via the Hardy.lean banks (lap-179's E–W Lemma-19 two-sided
  brackets + ε₀-diagonal capstone — banked FOR this rung); contradict with the banked lower
  bound (`goodsteinLength_dominates_fastGrowing`). `wainer_bound_of_pa_proves_goodstein`
  flips `axiom → theorem`; ledger 14 goes clean. Est. 2–4 laps @ 75%.
- **C — the crown re-point** (ledger 16, `pa_not_proves_goodstein`): the summit
  `peano_not_proves_goodstein` has ZERO intrinsic work — it currently proves the proposition
  through the banked Route-A axiom, and `peano_not_proves_goodstein_growth` states the
  **literally identical** proposition `𝗣𝗔 ⊬ ↑goodsteinSentence`. When `routeB_headline` goes
  clean (rungs above + W7), the summit's body re-points
  `:= peano_not_proves_goodstein_growth` and the machine audit flips it green. The Route-A
  body stays banked under its own name. Est. 1 lap @ 95%. (This answers "how does the crown
  go green if it has no laps": its laps live entirely in its dependency chain — by design.)

Sum ≈ 20–40 laps; overall discharge confidence now ~65% (up from 60: pins 1–2 done, read-off
proven, the pass redesign paper-grounded). The ladder's value: per-rung status/estimates on the
blueprint instead of one orange monolith, and after lap 8 the rungs P / D / E are largely
independent — parallel worktree grinds become an option (operator's call; coordination cost is
real).

## Blueprint representation (live as of 2026-07-02)

The ladder is ON the dep graph now: rungs P/D were already nodes (`thm:zeh_pass`,
`thm:zeh_readoff_delta0`); rungs R/E/W added as decl-less aspirational nodes
(`thm:zeh_rank_zero`, `thm:zeh_embedding`, `thm:wainer_splice`) with hand-note estimates
(NODE_NOTE in `blueprint/annotate_depgraph.py`), wired E→(P)→R→D→W→`thm:wainer_axiom`; rung C =
ledger row 16 on the summit. Ledger row 14 (`wainer_axiom`) re-based `30-60@60` → `20-40@65`
(the rung sum). Rung statuses are hand-claims until the lap-8 port erects the named pins with
their own ledger rows — at which point row 14's estimate collapses into the rungs' machine rows.

## Sequencing

1. **Lap 7** (next fire, wip-only): `Zef2` + `ewIter` statement lap per the entrance order.
2. **Lap 8** (judged port): `Zef2` into src, pins 1–2/inversions/embedding/read-off re-proven,
   **and erect this ladder** — five named pins (LOCK R5: disclosed, named laps), per-rung
   `@[goodstein_blueprint]` attributes replacing the single wainer node's estimate, so
   `blueprint_audit` + the reconciler track rung-level progress by machine.
3. **Laps 9+**: grind rungs (P first; D parallelizable; E after its seam plan ratifies).

## Non-negotiables carried over

Full-discharge-or-abandon (2026-07-01 mandate) — the ladder is decomposition, NOT
axiom-acceptance; every rung must eventually be a sorry-free theorem. No rung statement is
ratified until its statement lap survives the judge. Frozen surfaces + FORBIDDEN lists of the
lap-7 entrance order unchanged.
