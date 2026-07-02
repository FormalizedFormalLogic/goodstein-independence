# REBUILD-Z SERIES-1 — run ledger (append-only, one block per stage)

Pipeline per `REBUILD-Z-SERIES-1-ORDER-2026-07-02.md`. This file is what the judge reads first at
series end. Terse + honest. Commit per stage.

Headline invariant (checked each stage): `GoodsteinPA.peano_not_proves_goodstein` =
`[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]` — UNDRIFTED.

---

## Stage 1 — statements + seam probe (lane P statements)  · STATUS: IN PROGRESS

**R-0 seam probe (`wip/Lap10SeamProbe.lean`) — LANDED, T-S1 PASSES.**
The judge's `α + γ` reduction output (no `osucc`, no `+1`) is kernel-verified to discharge all
three reduction seams. All `#print axioms`-clean:
- (i) `seam_add_lt_add_left` / `seam_lt_add_of_pos` — strict left-covariance of ONote `+` on NF
  (`Zekd.add_lt_add_left_NF` + `repr_add`); premises land strictly below `α + γ`.
- (ii) `seam_ewN_add_comp` — `ewN α ≤ g 0 → ewN γ ≤ f 0 → (∀k, g0+k ≤ g k) → ewN (α+γ) ≤ g (f 0)`
  (the lap-9 `noOsucc_closes` pattern over the additive norm; `ewN_add_le` + base floor).
- (iii) `seam_complexity_nm` (`(φ/[nm n]).complexity = φ.complexity`) + `seam_cutRead_comp`
  (`c₀ ≤ f 0 → (∀x, x ≤ g x) → c₀ ≤ (g∘f) 0`) — the fresh cut-read gate closes.

**Promoted to `src`** (reusable Stage-2 content):
- `EwIter.base_add_le_comp` — pure-ℕ base-additive lemma.
- `OperatorZef2.ewN_add_le_comp` — `ewN`-level composite gate (`ewN_add_le` + base lemma).

**R-1 Pin 1 `cutReduceAllAuxRunning_Zf2` — RESTATED VERBATIM** (α+γ output; +`hg_base`,
+`φ.complexity ≤ f 0`; docstring supersedes osucc form per ruling §3/trap 9/E–W L25). Body `sorry`.

**R-2 Pin 2 `stepAllω_Zf2` — RESTATED VERBATIM** (+`hg_base`, +`hχRead`). Body `sorry`.

**Gates**: build 🟢 1341 jobs · headline UNDRIFTED · no new axiom · no native_decide.
**Commit**: (this checkpoint).

**REMAINING in Stage 1** (next checkpoints): R-4 (L-D restate + `<BoundedInstance>` probe ≥2
candidates), R-5 (new `WainerLadder.lean`, wire blueprint root + `mk_all`), R-6 (DELETE
`embedding_Zef2`), blueprint `\lean{}` re-point + `blueprint_audit`.

---

## Stage 2 — pins 1–2 grind (gate: R-0 passed)  · STATUS: LANDED

**Pin 1 `cutReduceAllAuxRunning_Zf2` — DISCHARGED, axiom-clean** `[propext, Classical.choice,
Quot.sound]`. Ported the proven `Zef` skeleton (`OperatorZeh.lean:1528` `cutReduceAllAuxRunning_Zf`)
over `Zef2` with:
- output ordinal `osucc (α+γ) → α+γ` (judge ruling); the old `Zekd.add_osucc_descent` descents
  become the strict-covariance `Zekd.add_lt_add_left_NF` (R-0(i) seam), and the principal-cut
  `α < osucc(α+γ)` becomes `α < α+γ` via the new `lt_add_of_inner_lt` (needs `0 < γ`, witnessed by
  the exI descendant `β < γ`);
- the `ewN` gate re-threaded at EVERY rebuilt node: fresh roots close via `ewN_add_le_comp hg0 hαN
  hg_base` (R-0(ii)); the shared `hg0 : ewN α ≤ g 0` is read off `fam 0`'s gate;
- the fresh cut-reads close via `hφread`/`hcutRead' → hg_infl` (R-0(iii));
- `Zef2Prov`'s extra gate field threads through every witness (`.choose_spec` index shift
  `.2.2.2 → .2.2.2.2`).
Needed `set_option maxHeartbeats 1000000` (gate terms enlarge the induction).

**Pin 2 `stepAllω_Zf2` — DISCHARGED, axiom-clean** `[propext, Classical.choice, Quot.sound]`.
Short composition: invert the ∀-side `D₁` to the running family via `allInv_Zef2`, feed pin 1
against the ∃-side `D₂`; output `δ = α₁ + γ₁`.

**Gates**: build 🟢 1341 jobs · headline UNDRIFTED · pins `#print axioms` clean · no new axiom · no
native_decide. **Commit**: (this checkpoint). Lane P now advances to Stage 3 (THE PASS grind).

---

## Stage 3 — THE PASS grind (`cutElimPass_Zef2`)  · STATUS: IN PROGRESS (crux de-risked)

The pass (E–W Lemma 26/27, predicative cut-elimination) is the concentrated-risk girder. The old
`Zef` pin-3 (`cutElimPass_Zf`) was ALSO never proven, so this is written from scratch. This lap
DE-RISKED the two decisive containments the cut-elimination step needs and banked them to `src`.

**Cut-elim step structure** (induction on `D : Zef2 α e H f (c+1) Γ`): at a top-rank cut with
premises at `βφ,βψ < α`, the IH gives rank-`c` derivations at `collapse βφ`, `collapse βψ` with
slots `ewIter f βφ`, `ewIter f βψ`; the reduction pin (`stepAllω_Zf2`) merges them → ordinal
`≤ collapse βφ + collapse βψ`, slot `ewIter f βφ ∘ ewIter f βψ`. Both must fit under the declared
output `collapse α = ω^α` / `ewIter f α`.

**BANKED (both `#print axioms`-clean, `wip/Lap10PassProbe.lean` → `src`):**
- `OperatorZef2.collapse_add_lt` — ordinal side: `βφ,βψ < α → collapse βφ + collapse βψ <
  collapse α` (additive principality of `ω^α`). Ordinal side of the cut step is DONE.
- `EwIter.ewIter_le_of_lt` — **gated ordinal-monotonicity of `ewIter`**: `β < α`, gate
  `ewN β ≤ f (ewN α + m)` ⟹ `ewIter f β m ≤ ewIter f α m`. The ewN gate RESTORES exactly the
  property trap-8 refuted for bare `iterSlot`. This is the key that un-walls the slot side.

**BANKED (slot side now COMPLETE, axiom-clean, `wip/Lap10PassProbe.lean` → `EwIter.lean`):**
- `EwIter.ewIter_comp_le` — the slot-composition lemma `ewIter f α₀ (ewIter f α₁ m) ≤ ewIter f α m`
  for `α₀,α₁ < α` (NF), from base gates `ewN αᵢ ≤ f 0` + monotone/infl. Proof: ONote-order
  trichotomy → δ = larger (< α) → gated mono lifts both → two-fold `ewIter f δ (ewIter f δ m)` →
  `ewIter_lower` at δ<α collapses to one-fold. The gate bookkeeping collapsed to trivial
  (`f 0 ≤ f _`), no pass-invariant threading needed.

**Cut-step containments COMPLETE**: ordinal (`collapse_add_lt`) + slot (`ewIter_comp_le`) both
proven. The cut-elimination step of the pass is now arithmetically de-risked end-to-end.

**BANKED (node-gate + slot-lift, axiom-clean, `wip/Lap10PassProbe.lean` → `src`):**
- `EwIter.ewIter_slot_le` — pointwise slot lift `ewIter f β x ≤ ewIter f α x` (β<α) for
  `Zef2.mono_f` at internal nodes.
- `OperatorZef2.ewN_collapse` (`ewN (collapse α) = ewN α + 1`) + `OperatorZef2.ewN_collapse_le`
  (per-node gate `ewN (collapse α) ≤ ewIter f α 0` from base gate + `EwF1 f`).

**Pass-prep engine COMPLETE.** All containment/gate/lift lemmas the pass induction needs are proven
and banked: `collapse_add_lt`, `collapse_strictMono` (existing), `ewIter_le_of_lt`, `ewIter_comp_le`,
`ewIter_slot_le`, `ewIter_monotone`/`_infl` (existing), `ewN_collapse_le`.

**KEY UNBLOCK — `EwLow` (`2m+1 ≤ f m`) threads through `allω`, not `EwF1`.**  The pass CANNOT
require `EwF1` of the slot: `allω` branches carry `rel1 f n`, and `rel1`'s `max`-plateau BREAKS
strict monotonicity (the order's flagged wall).  But `ewN_collapse_le` (the per-node gate) needs
only the `EwF1` *second* component `2m+1 ≤ f m` — and `rel1 f n` PRESERVES that
(`f(max n m) ≥ f m ≥ 2m+1`, banked `rel1_low`).  So the pass threads `Monotone + infl + (2m+1≤·)`,
all three `rel1`-stable → the induction recurses into `allω` branches with NO `EwF1`-of-relativized
demand.  **The order's halt-and-escalate wall does NOT fire.**

**BANKED (src):** `ewN_collapse_le` weakened to the `hlow : ∀m,2m+1≤f m` hypothesis;
`OperatorZeh.rel1_low` (`rel1` preserves the `2m+1` bound).

**ASSEMBLED IN SRC — `OperatorZef2.passAux`** (the pass as a generalized-rank induction) with
`cutElimPass_Zef2` now a REAL derivation from it (no longer a bare `sorry`).  3 of 6 cases
DISCHARGED axiom-clean (validated first in `wip/Lap10PassProbe.lean`):
- `axL` — build at `collapse α`, node gate `ewN_collapse_le`;
- `wk` — IH + `Zef2Prov.weakening`;
- `weak` — IH at β<α + `collapse_strictMono` (ordinal) + `ewIter_slot_le` (slot).

**REMAINING (3 named sub-`sorry`s in `passAux`, the crux decomposition):**
- `exI` — like `weak` + rebuild the `∃` node; bound `n ≤ ewIter f α 0` (need `f 0 ≤ ewIter f α 0`).
- `allω` — ω-branch reassembly: IH at `rel1 f n` branches (invariants via `rel1_monotone`/`_infl`/
  `rel1_low`), recombine into `ewIter f α` via `ewIter_rel1_le`.
- `cut` — sub-rank (χ.complexity<c) rebuild; TOP-rank (=c) eliminate via `stepAllω_Zf2` +
  `collapse_add_lt` + `ewIter_comp_le`. ⚠️ c=0 ATOMIC cut still needs an atom-cut lemma.

**Gates**: build 🟢 1341 jobs · headline UNDRIFTED · all lemmas axiom-clean · no new axiom.

---

## Stage 3 — lap 11 (191): `passAux` 5/6; top-rank CUT hits the `hg_base` floor seam

**DISCHARGED (green, axiom-clean):** `exI`, `allω`, `cut`-SUB-RANK (`χ.complexity < c`) — see
`passAux` in `OperatorZef2.lean`. Banked `stepAllω_Zf2_bnd` (bound-exposing `δ ≤ P₁+P₂` principal
∀/∃ reduction). `passAux` now 5/6; sole remaining sub-`sorry` = TOP-RANK cut (`χ.complexity = c`).

**SEAM FOUND (kernel-clean, `wip/Lap11CutFloorProbe.lean`) — the top-rank discharge as designed does
not fire.** `stepAllω_Zf2` requires `hg_base : ∀k, g 0 + k ≤ g k` on the reduced ∀-side slot
`ewIter s βφ`. The pass's `rel1`-stable invariant (`Monotone ∧ infl ∧ 2m+1≤s m`) does NOT entail it:
- `basefloor_not_rel1_stable` — `rel1 (2m+1) 3` meets the invariant, violates the floor (`8 > 7`).
- `ewIter_one`/`ewIter_one_floor_fails` — floor fails even at PRINCIPAL `β=1` (`ewIter s 1 = s∘s`,
  singleton ball, inherits the plateau). Refutes the ball-growth escape.

**LIVE RESOLUTION (PROOF-only, lane B):** re-gate `cutReduceAllAuxRunning` via the `2m+1` floor on
`ewIter s βφ` (`g(f'0) ≥ 2f'0+1`) + a tight family-ordinal bound `ewN α₁ ≤ s 0 + 1`, replacing
`hg_base` — no statement change. **Open sub-problem:** the tight bound `ewN(witness) ≤ f 0 + 1` is
inductive through every `passAux` case EXCEPT top-rank `cut` output (`ewN ~ 2f0+2`). Next lap: relax
it for cut outputs, or prove a principal cut's ∀-premise reduces to a collapse-shaped tight-norm
witness. If unclosable → statement escalation (judge-gated); do NOT self-ratify.

**Gates:** build 🟢 · headline UNDRIFTED · all landed lemmas axiom-clean · no new axiom · probe
`wip/`-only (not in build).

---

## REVIEW — lap 192 (fresh-mind): top-rank cut escalation UPHELD + SHARPENED; lane B REFUTED

**No new src code.** Independent re-verification (real `#print axioms`, build 🟢 `GoodsteinPA`):
headline `[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]`, sorryAx OFF, no
drift. The lap-191 escalation of the top-rank cut (`OperatorZef2.lean:748`) is **correct** — the
Stage-3 order's pre-registered `rel1`/(f.1) base-additivity wall fired. Two sharpenings for the
series-end judge pass:

1. **Lane B is REFUTED** (was scoped in lap-11 as the "PROOF-only resolution to pursue next"). The
   floor route needs `ewN(∀-witness) ≤ f0+1`, but the reduction only bounds it by the ∀-slot base
   `g0` (un-absorbable by the `2m+1` floor), and the bound is non-inductive: `ewN` grows additively
   under the `α+γ` output while `ω^α` absorbs the ordinal, so nested top-rank cuts blow `ewN(witness)`
   up ~`2^d·(f0+1)`. Lane B does not close; do not re-open it.

2. **The obstruction is a TRILEMMA among ratified pillars**, not a fixable proof gap. The node gate
   `ewN(α+γ) ≤ g(f0)` closes iff one of: (a) an **absorbing norm** `ewN(α+γ)=max(ewNα,ewNγ)` — breaks
   the finite-fiber requirement that forced `ewN` (T-Z7(i)); (b) **base-additivity** of the ∀-slot —
   destroyed by `rel1 f n = f(max n·)` in nested ω-contexts, and `rel1` max→+ recovers it only for
   strictly-monotone `g` (which `ewIter` lacks, trap-8 plateau); (c) a **non-additive output ordinal**
   — fixed at `α+γ` by ruling #1. **JUDGE AMENDMENT MENU:** the prime candidate is (a) — *does a
   finite-fibered absorbing norm exist?* (a `max`-based CNF rank has infinite fibers, so this is a
   real design question). Grind laps may probe it wip-only; never port to src.

**Productive lane (this review's mandate):** lane D `readoff_delta0_Zef2` — independent of the
escalated crux. See DIRECTION.md CURRENT DIRECTIVE (lap-192 block) + PENDING_WORK.md (lap-192 top).
