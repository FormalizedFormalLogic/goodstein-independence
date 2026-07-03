# REBUILD-Z — SERIES-3 ORDER: the post-ruling GRIND (architect, 2026-07-03) 🔒

> **Binding.** Issued with `E-2026-07-03-JUDGE-series2-validation.md` (Series-2 PASS; both
> amendment rulings made). This is the LONG grind series the rulings unblock — **every open
> rung of the Wainer ladder is now workable**: the pass's top-rank cut (Lane N), rung R's flip
> (in-lane), rung D (Lane D), rung E (Lane E, wip-first), the splice (Lane W). Operator
> directive: fill the fire's whole budget with productive work; walk the ladder DOWN on blocks;
> stop ONLY when every lane is landed-or-blocked-with-escalation. An idle or padding lap is a
> violation; so is stopping while any lane has in-scope work.
>
> Safety invariants unchanged: ratified statements are verbatim (the ewN→Nlog substitution
> images are pre-ratified BY CONSTRUCTION — zero authoring freedom); rung-E's statement stays
> wip until judge-ratified; self-ratification VOID; ledger claims diff-verified;
> **bare `lake build` is the only valid gate**.

Maintain `REBUILD-Z-SERIES-3-LEDGER.md` (append-only, block per stage/lane-advance, commit per
block). Baseline for the judge's diffs: the HEAD this order is committed at.

## Lane N — the norm swap + THE PASS (highest value; unblocks R in-lane)

- **(N-0) T-S3 ENTRY GATE (HARD; wip/NlogGateProbe.lean; no src swap until it passes).**
  Kernel-discharge the cut-node slack from the threaded kit: for `g = ewIter s βφ`,
  `f = ewIter s βψ` (s = the node slot, Monotone + infl + EwLow; node gates available),
  `max (g 0) (f 0) + c ≤ g (f 0)` for the probe's absorption constant `c` — **INCLUDING the
  edges `βφ, βψ ∈ {0, 1}`** (the judge found `βψ = 0` ⇒ `f 0 = 0` ⇒ hslack false as stated; if
  an edge genuinely fails, prove the case-split dodge instead: e.g. a `βψ = 0`/rank-0-ordinal
  premise handled by direct weakening with NO reduction — kernel-check that branch closes).
  Also required in N-0: `Nlog_collapse`/`Nlog_collapse_le` analogs (per-node + Def-16 iterate
  gates over `Nlog`), and a pins-1–2-over-Nlog miniature (one axL + one fresh-root case with the
  absorbing arithmetic). T-S3 failure on BOTH the direct and case-split forms ⇒ Lane N falls
  back to the ratified shift package {`rel1'`, `StepAdd`} (Ruling (1) fallback; measured
  new-inductive cost) — ledger the pivot, don't halt the series.
- **(N-1, gated on N-0)** Execute the **in-place** judged amendment: `Zef2`'s gate norm
  `ewN → Nlog` (no constructor shape change; `rel1` + `α+γ` untouched). Promote `Nlog`,
  `Nlog_add_le_max_succ`, `Nlog_finite_fiber` (NF form), `absorbing_closes_gate` from the probe
  to src. Re-grind the suite on the Series-1 templates: pins 1–2, the gate lemma stack
  (`absorbing_closes_gate` replaces `ewN_add_le_comp` at fresh roots), the read-off exits
  (toZef is gate-forgetting — re-check, expected mechanical), `passAux`'s five proven cases.
  Every restated statement = the ratified text under the substitution; ledger each with its
  sweep.
- **(N-2)** **THE TOP-RANK CUT** — the reserved crux, now unblocked: IH both premises to rank
  `c`, merge via `stepAllω_Zf2`/`_bnd`, land under `collapse α` via `collapse_add_lt` +
  `ewIter_comp_le` + the N-0 gate arithmetic. The `c = 0` atomic sub-crux: the flagged atom-cut
  lemma (axL-pair surgery). `passAux` 6/6 ⇒ `cutElimPass_Zef2` CLEAN — sweep must show the
  standard triple.
- **(N-3)** Rung R flips: re-sweep `rankToZero_Zef2` (expected standard triple, automatic),
  blueprint rung R node back to honest status (restore `\notready` first — judge ruling §4.2 —
  then let the reconciler flip it green when clean), `blueprint_audit`.

## Lane D — rung D lands (independent of N)

- **(D-3)** Execute **R-4′** (ratified verbatim in the ruling — copy it): restate
  `readoff_delta0_Zef2`'s conclusion to `∃ n ≤ ewIter f α 0`. Re-prove `readoffD_aux` at the
  achievable bound — the branch-0 mechanism carries over, and the trapped case now closes
  structurally (`ewIter_lower` aggregation, per the lap-195 algebra). Retire `readoffD_trapped`
  (delete or subsume; `readoffD_trapped_of_mono` stays as a src lemma — it is true, just not
  goodstein-applicable). Target: `readoff_delta0_Zef2` sweep = standard triple.
  ⚠️ If Lane N's swap lands first, do D-3 over the Nlog calculus (one re-grind, not two);
  if D-3 lands first, N-1's re-grind covers it. Coordinate via the ledger — whichever is
  in-flight first owns the file.

## Lane E — rung E: statement + wip grind (the long pole; B-2 debt)

- **(E-0)** The rung-E statement DRAFT (B-2 debt, first item): the W3-ratified K-hypothesis
  shape re-based onto the current calculus, source hypothesis
  `hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence`, `Γ_G` bound to the CONCRETE goodstein translation, homed in
  `WainerLadder.lean` — **text in wip (docstring or probe file), NOT src**, with a one-block
  ledger justification. Alongside it, the **Ax2-need kernel probe**: embed ONE concrete PA-axiom
  leaf / true-Δ₀ leaf of the translation into `Zef2` vs `Zef2T` — does closure require the
  true-literal rule? (B(iii) predicts yes; prove it either way.) That answer + the draft go to
  the next judge pass; **(Ax2) adoption is ruled there** (its costs are already measured:
  reduction mechanical, read-offs native re-proof).
- **(E-1)** Wip grind AGAINST the draft (sanctioned — wip theorems are ruling inputs): the E–W
  Lemma 32–36 mechanisms — leaf embeddings, the induction-axiom case, K-hypothesis composition,
  budget bookkeeping — built as real kernel content in `wip/EmbeddingGrind*.lean` importing src.
  Estimate honestly (the graph says 8–20 laps for the full rung); every lap banks named lemmas.
  Promotion to src happens after the statement is judge-ratified — do NOT let that gate idle the
  lane.

## Lane W — the splice composes as rungs land

- **(W-1)** Compose `wainer_splice_Zef2` (ratified R-5 shape, in src) against whatever rungs are
  real: R (after N-3) and D (after D-3) consume in src; E consumes from the wip grind only as a
  clearly-marked wip composition (`wip/SpliceAssembly.lean`) until E is ratified. The Hardy
  Lemma-19 brackets + C-1's `rfl` tower conversion are banked. The src `sorry` shrinks to
  exactly the rung-E consumption point.

## PRODUCTIVITY LADDER (walk down on blocks; never idle)

**N-0 → N-1 → N-2 → {N-3, D-3, E-0} → E-1/W-1 → probe-deepening (sharpen any escalation to
ruling grade) → hygiene (lap-tail ONLY).** Lanes D and E are independent of N — a Lane-N wall
is a license to advance them, not to stop. Route-A/`Zf`-era sorries stay FROZEN.

## STOP RULE

Stop ONLY when: every lane is landed or blocked-with-a-kernel-escalation, and no wip
deepening would change a future ruling. With Lane E in scope this series has 10+ hours of
genuine work; an early stop should be *surprising* and must be justified in the ledger's final
block, lane by lane. `done --green` after the final commit; the host verifies the full gate.

## Gates (every block)

Bare `lake build` 🟢 · headline `peano_not_proves_goodstein` quadruple UNDRIFTED (it routes via
Route A — the norm swap must not touch it) · sweep every landed theorem (standard triple or
named sorryAx path) · `lean-sorry src/` delta ledgered exactly, survivors named · NO new
`axiom` · NO `native_decide` beyond the blessed base · statements = ratified texts or their
`ewN→Nlog` substitution images ONLY · wip freeze refs (`wip/EwIter.lean`, `wip/Zef2Calculus.lean`)
untouched · `blueprint_audit` passes · ledger block per advance, claims diff-verifiable.

## FORBIDDEN

Statement text with authoring freedom (only: ratified texts, substitution images, R-4′ as
given, wip drafts marked DRAFT). (Ax2)/`Zef2T` in src (E-0 probes only, wip). `rel1` changes in
src unless Lane N pivots to the ratified fallback (then the shift package executes as its own
judged block, ledgered as such). Touching Route-A surfaces. Self-ratification (VOID).
Un-diff-verified ledger claims. Idle/padding laps.

## Fire shape (operator)

`--max-laps 12 --max-duration 10h --review-every 3 --allow-stop` (grind estimates run 2–4×
optimistic; the lap/duration caps bound it; Lane E alone can absorb any surplus). Expected
value: N-2 lands the pass (⇒ rungs P+R go green), D-3 lands rung D, E banks the draft + probe +
early embedding bricks, W shrinks the splice sorry to the E-seam — with the next judge pass
ruling (Ax2) and ratifying the rung-E statement.
