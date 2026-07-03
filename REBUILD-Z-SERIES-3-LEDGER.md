# REBUILD-Z — SERIES-3 LEDGER (append-only; block per stage/lane-advance)

Order in force: `REBUILD-Z-SERIES-3-ORDER-2026-07-03.md`.  Baseline for judge diffs: `1e29f64`
(the HEAD the order was committed at).

---

## Block 1 — (N-0) T-S3 ENTRY GATE: **PASSES** (direct form; NO case-split dodge needed)

**Lap**: 198 · **Files**: `wip/NlogGateProbe.lean` (NEW, standalone probe, wip-only; `src`
untouched) · **Build**: 🟢 bare `lake build` (1342 jobs) · **Headline**: untouched (no src
delta; `lean-sorry src/` delta = 0).

**The gate demand** (order N-0): kernel-discharge the cut-node slack
`max (g 0) (f 0) + c ≤ g (f 0)` for `g = ewIter s βφ`, `f = ewIter s βψ`, `s` the threaded kit
slot (Monotone + inflationary + EwLow), `c = 1` (Nlog's absorbing constant), **including the
edges `βφ, βψ ∈ {0, 1}`** the judge flagged (`βψ = 0 ⇒ f 0 = 0 ⇒ hslack false as stated`).

**Result: the DIRECT form holds for ALL `βφ, βψ` — the flagged edge is vacuous and no
case-split dodge is required.**  Two structural facts:

1. **Edge vacuity** (`kit_f0_pos`, `ewIter_base_le`): the EwLow floor makes
   `f 0 = ewIter s βψ 0 ≥ s 0 ≥ 1` for every `βψ` — at the flagged edge `βψ = 0` we get
   `f 0 = s 0 ≥ 2·0+1 = 1`, never `0`.  The judge's degeneration presupposed a generic `f`
   with `f 0 = 0`, which the threaded kit never produces.
2. **The swap lemma** (`ewIter_swap`, the lap's structural insight — NEW, not in any prior
   probe): `s (ewIter s α x) ≤ ewIter s α (s x)` for every Monotone + inflationary `s` and
   EVERY `α`.  Proof: well-founded recursion on `α` through a new max-attainment primitive
   `ewIter_attained` (the `ewStep` max is realized on a gated branch `β < α`; extracted via
   `Finset.max'_mem`), chaining IH twice with `ewIter_monotone` and closing by `ewIter_lower`
   with the gate transported along `x ≤ s x`.  This converts the `g`-arm's needed strict gain
   into EwLow arithmetic **without strict monotonicity** — the trap-8 plateau obstruction (the
   reason `hg_base` was refuted for `ewIter` slots) dissolves because the argument bump
   `0 → f 0 ≥ s 0` is itself a slot application, and `ewIter` one-sidedly commutes with its
   own slot.

**hslack** (`hslack_kit`): `f`-arm by `ewIter_low` (`g (f 0) ≥ 2·f 0 + 1`); `g`-arm by
`g (f 0) ≥ g (s 0) ≥ s (g 0) ≥ 2·(g 0) + 1` (monotone + swap + EwLow).  Explicit edge
corollaries `hslack_kit_edge_00`, `_psi0`, `_11`.

**Also delivered (the rest of the N-0 bill)**:
- `Nlog_collapse` (= `Nlog α + 1`) and `Nlog_collapse_le` — the per-node pass gates over
  `Nlog`, exact analogs of `ewN_collapse`/`ewN_collapse_le` (same `f (f 0)` mechanism, only
  EwLow, `rel1`-surviving).
- `ewIterTower_infl/_monotone/_low` + `Nlog_collapseIter_le` — the Def-16 iterate/tower gate
  (rung R's per-pass node gate iterates down the rank).
- **Pins-1–2 miniature**: `Nlog_add_le_comp_kit` — the fresh-root gate
  `Nlog (α+γ) ≤ g (f 0)` at the ACTUAL kit slots, closed by `Nlog_add_le_max_succ` (the D-1
  absorbing theorem, copied verbatim — wip probes are standalone; N-1's src promotion is the
  dedup point) + `hslack_kit`, with **no `hg_base` anywhere**; `MiniZ.axL` + `mini_axL` +
  `mini_axL_fresh_root` — one axL and one rebuilt fresh-root case over the `Nlog` gate.

**Sweep** (`#print axioms`, all `[propext, Classical.choice, Quot.sound]`): `ewIter_swap`,
`hslack_kit`, `Nlog_add_le_comp_kit`, `Nlog_collapseIter_le`, `mini_axL_fresh_root`,
`Nlog_add_le_max_succ`.  No `native_decide`, no new `axiom`, no sorryAx.

**Consequence**: the Lane-N fallback (shift package {`rel1'`, `StepAdd`}) is NOT needed.
**N-1 (the in-place `ewN → Nlog` src swap) is UNBLOCKED.**

**N-1 design note surfaced by this block** (for the re-grind): the slot-lift plumbing
(`ewIter_slot_le`, `ewIter_comp_le`, the `allω` gate transfer in `passAux`) consumes
`ewN β ≤ f 0` gates from `Zef2.gate`.  After the norm swap the calculus hands back
`Nlog β ≤ f 0`, which does NOT bound `ewN β` (`Nlog ≤ ewN`, wrong direction).  So N-1 must
also swap `ewIter`'s internal ball/filter norm to `Nlog` (NF-restricted ball via
`Nlog_finite_fiber`.toFinset — `ewIter` is already noncomputable) and re-grind the `EwIter`
lemma suite on the same templates (`ewIter_lower` picks up an `NF β` hypothesis; all call
sites carry NF).  `ewIter_attained` + the swap lemma templates carry over unchanged.

---

## Block 2 — (N-1) THE NORM SWAP EXECUTED: `Zef2`'s gate norm `ewN → Nlog`, in place, suite re-ground

**Lap**: 198 · **Files**: `src/GoodsteinPA/EwIter.lean`, `src/GoodsteinPA/OperatorZef2.lean` ·
**Build**: 🟢 bare `lake build` (1342 jobs) · **`blueprint_audit`**: ✓ PASSED (16 nodes, 0
warnings) · **Headline**: `peano_not_proves_goodstein` = `[propext, Classical.choice,
goodstein_implies_consistency, Quot.sound]` — **UNDRIFTED** · **`lean-sorry src/` delta: 0**
(OperatorZef2 keeps exactly its 2: `passAux` top-rank cut :~750, `readoffD_trapped`).

**Promotions to src (EwIter.lean)** — all statements are the probe texts (ratified by
construction): `clog` + `clog_add_le`/`clog_pos`/`coe_lt_of_clog_le`, `Nlog` + simp lemmas,
`Nlog_finite_fiber` (NF form) + `NlogBall` (its `Finset`, via `.toFinset`) + `mem_NlogBall`,
`Nlog_add_le_max_succ`, `absorbing_closes_gate` (generic) + `Nlog_add_le_comp` (instance form),
`ewIter_attained`, `ewIter_swap`, `ewIter_base_le`, `hslack_kit`, **`hslack_kit_ge`** (NEW: the
`∀ k ≥ f 0` slot-threaded form — see design note below).

**The in-place swap**:
- `ewStep`'s branch ball: `ewBall`+`ewN` filter → `NlogBall`+`Nlog` filter (substitution image;
  the NF restriction is forced by `Nlog`'s fiber structure and is the population the calculus
  feeds anyway).  `ewIter`'s recursion/termination unchanged.
- `EwIter` suite re-ground on the same templates: `ewIter_lower`/`_le_of_lt`/`_slot_le`/
  `_lift(_of_mono_infl)`/`P1_ewIter_lift` gain an `NF β` hypothesis (Block-1's design note,
  realized); `_infl`/`_low`/`_monotone`/`_comp_le`/`_rel1_le` mechanical (`NF` for branch
  ordinals comes free from `mem_NlogBall`).
- `Zef2` constructor gates: `hαN : ewN α ≤ f 0` → `Nlog α ≤ f 0` (6 constructors), `gate`,
  `Zef2Prov`, `gate_rel1`, `allInv_Zef2` — mechanical.
- **The judged replacement at fresh roots**: `cutReduceAllAuxRunning_Zf2` drops
  `hg_base : ∀ k, g 0 + k ≤ g k` (the kernel-refuted base-additivity) and instead threads
  `hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k` INSIDE the induction statement (design forced:
  the slack is slot-dependent where `hg_base` was not; the `∀ k ≥ f 0` form transfers down the
  `allω` `rel1 f n` re-entries since slot bases only grow: `rel1 f n 0 = f n ≥ f 0`).  All ~15
  fresh-root gates now close by `Nlog_add_le_comp` (absorbing + slack); `stepAllω_Zf2`/`_bnd`
  restated with `hg_slack` in place of `hg_base`.
- `passAux`/`rankToZeroAux`: node gates `ewN_collapse_le` → `Nlog_collapse_le` (promoted next
  to `ewN_collapse_le`, which stays as frozen `ewN` evidence together with the whole
  `ewN`-arithmetic bank).

**Sweep** (all `[propext, Classical.choice, Quot.sound]` unless noted):
`cutReduceAllAuxRunning_Zf2` ✓, `stepAllω_Zf2` ✓, `stepAllω_Zf2_bnd` ✓,
`readoff_sigma1_Zef2` ✓, `headline_readoff_Zef2` ✓, `Nlog_collapse_le` ✓,
`Nlog_add_le_comp` ✓, `hslack_kit_ge` ✓, `ewIter_swap` ✓, `Nlog_add_le_max_succ` ✓,
`Nlog_finite_fiber` ✓; `rankToZero_Zef2`/`cutElimPass_exit_root_Zef2` = `+ sorryAx` (the named
`passAux` top-rank path, expected — that is N-2's target, now with its gate arithmetic REAL:
the kit discharges `hg_slack` via `hslack_kit_ge`).

**KEY consequence**: the reduction and both `stepAllω` wrappers no longer carry ANY unprovable
slot hypothesis — `hg_slack` is a THEOREM of the kit (`hslack_kit_ge` at `g = ewIter s βφ`,
`f = ewIter s βψ`).  The trilemma's escalated horn is dead in src, not just in probes.
**N-2 (the top-rank cut) is now purely assembly**: IH both premises, `stepAllω_Zf2_bnd`,
`collapse_add_lt`, `ewIter_comp_le`, + the `c = 0` atom-cut lemma.

---

## Block 3 — (N-2) **THE TOP-RANK CUT IS CLOSED — THE PASS LANDS** (+ N-3 rung R flips)

**Lap**: 198 · **Files**: `src/GoodsteinPA/OperatorZef2.lean`, `blueprint/src/content.tex` ·
**Build**: 🟢 bare `lake build` (1342 jobs) · **`blueprint_audit`**: ✓ PASSED · **Headline**:
quadruple UNDRIFTED · **`lean-sorry src/` delta: −1** (`passAux`'s top-rank `sorry` GONE;
`OperatorZef2` survivor = `readoffD_trapped` only, reserved for D-3).

**The reserved crux — open since the lap-188 `osucc`-gate refutation, escalated lap-191,
trilemma'd lap-192, ruled lap-197 — is now a kernel theorem.**  Sweep:
- `passAux` = `[propext, Classical.choice, Quot.sound]` — **all 6 cases closed**;
- `cutElimPass_Zef2` (rung P / `thm:zeh_pass`) = standard triple — **REAL**;
- `rankToZero_Zef2` (rung R / `thm:zeh_rank_zero`) = standard triple — **REAL** (flipped
  automatically, exactly as the Series-1 ledger predicted);
- `cutElimPass_exit_root_Zef2` (the anti-vacuity composed exit) = standard triple;
- new helpers `atomCutRun_Zf2`, `Zef2.erase_inert` = standard triple.

**The proof (E–W Lemma 26 principal step, by cut-formula shape).**  The IH reduces both
premises to rank `c` at `(collapse βφ, ewIter f βφ)` / `(collapse βψ, ewIter f βψ)`; then:
1. **`∀`-shape** (`χ = ∀⁰ψ`): `stepAllω_Zf2_bnd` merges the premises (its `hg_slack` is
   DISCHARGED by `hslack_kit_ge` — the N-0 swap-lemma arithmetic, exactly as designed); the
   output ordinal `collapse βφ + collapse βψ` lands under `collapse α` by `collapse_add_lt`;
   the output slot composite lands under `ewIter f α` by `ewIter_comp_le`.
2. **`∃`-shape**: same with roles swapped (`∼(∃⁰ψ) = ∀⁰∼ψ` is `rfl`; `∼∼ψ = ψ` by simp).
3. **Atomic shapes** (`rel`/`nrel`) — the flagged sub-crux: **`atomCutRun_Zf2`**, the axL-pair
   surgery, built as a fixed-premise mirror of the running reduction: every axL leaf whose
   pair IS the cut atom is replaced by the (weakened) other premise; all other nodes rebuild
   at the fresh root `βψ + γ` with the absorbing gate `Nlog_add_le_comp` + the slot-threaded
   slack — the SAME `Nlog` machinery, no new hypotheses.
4. **Inert shapes** (`⊤/⊥/⋏/⋎` — cut formulas the order's shape list didn't enumerate, but
   which the full `Semiformula` type admits): NEW helper `Zef2.erase_inert` — these shapes are
   never principal in any `Zef2` rule (the calculus has no `⊤/⊥/⋏/⋎` rules), so they erase
   from any context with all gates riding; the cut premise then IS a derivation of `Γ`.

**(N-3)** `thm:zeh_pass` + `thm:zeh_rank_zero` flipped `\notready → \leanok` with honest prose
(status annotations, not ratified statement text); `blueprint_audit` ✓ 16 nodes consistent.

**Ladder state**: rungs P + R **GREEN**.  Remaining: D-3 (lane D, R-4′ restatement — retires
`readoffD_trapped`), E-0/E-1 (rung E statement + wip grind), W-1 (splice composition).

---

## Block 4 — D-3 EXECUTED: R-4′ landed verbatim — by VACUITY, not aggregation (lap 199)

**Claim (diff-verifiable):** `readoff_delta0_Zef2` (`src/GoodsteinPA/OperatorZef2.lean`) now
carries the R-4′-ratified conclusion `∃ n ≤ ewIter f α 0, atomTrue (φ/[nm n])` (statement text
= the ruling's verbatim form; zero authoring freedom exercised) and is **sorry-free on the
standard triple** `[propext, Classical.choice, Quot.sound]`.  The SOLE `OperatorZef2` sorry
(`readoffD_trapped`) is RETIRED.  Full `lake build` 🟢 (1342 jobs); headline quadruple
UNDRIFTED; `blueprint_audit` ✓ (16 nodes, `thm:zeh_readoff_delta0` flipped `\leanok`).

**HOW — the ordered route was impossible; the rung is VACUOUS (kernel-proven):**

1. **The order's aggregation plan FAILS.** "Trapped case closes via `ewIter_lower`
   aggregation" hits the lap-195 `k₀` wall unchanged: the false-branch index `k₀` is the
   least false matrix instance — SEMANTIC, bounded by no gate.  Adversary (prose, recorded in
   `wip/D3SpineProbe.lean`): matrix `x < N`, `Γ₀ = {∃⁰φ, ∼(φ/[nm N])} ∪ {∼(χ/[nm i]) : i<N}`,
   `φ = (x = N)`, `f = ·+1`, `α = 2` — the aux dichotomy holds, the derivation exists, the
   sole witness is `N ≫ ewIter f 2 0`.  The general-context aux-at-`ewIter`-bound is FALSE.
2. **What IS true — lap-195's flagged "residue vacuous" alternative, globalized.**  NEW src
   machinery: `spineHead` (strip the `∀/∃` spine, report terminal polarity + rel symbol;
   `⊤/⊥/⋏/⋎` = none), `spineHead_rew` (substitution-invariant), and
   `zef2_rank0_uniform_spine_underivable`: a uniform-spine sequent has NO rank-0 `Zef2`
   derivation — the sole leaf `axL` needs a complementary pair, but `allω`/`exI` insert only
   spine-head-preserving instances, and `Zef2` has no (Ax2) true-literal leaf and no
   `⊤/⋏/⋎` rules.  Corollary `zef2_rank0_singleton_ex_underivable`: `{∃⁰φ}` underivable at
   rank 0 for EVERY φ.  All standard-triple.  R-4′ then holds vacuously (`(·).elim`).
3. **Retirement:** the falsity-invariant scaffold (`readoffD_aux` + `readoffD_trapped`) moved
   VERBATIM to `wip/ReadoffDAuxRetired.lean` (frozen evidence; its sorry is designated-retired,
   not open).  `readoffD_trapped_of_mono` STAYS in src (ordered; true, goodstein-inapplicable
   per C-2).  `sound0`, `atomTrue_all_iff/ex_iff` stay (general lemmas).

**Ruling-relevant fallout (E-0 input, judge-owned):** rung D is CONTENT-FREE over `Zef2`.
`wip/D3SpineProbe.lean` adds the any-rank corollary `zef2_singleton_ex_underivable_anyRank`
(compose rung R + vacuity: `Zef2` cannot derive `{∃⁰φ}` at ANY cut rank under the rung-R side
conditions; standard triple).  So the rung-E embedding CANNOT target `Zef2` — it needs the
(Ax2)-extended `Zef2T`, exactly the Stage-B B(iii) prediction, now proven at the source rather
than probed at a leaf.  The pipeline's real load then runs: embedding in `Zef2T` → (Ax2)-aware
pass/read-off re-proofs (costs already measured, Stage B).  NOT self-ratified: R-4′ landed as
ratified; the `Zef2T` adoption decision stays with the rung-E ruling.

**Ladder state**: rungs P + R + **D** GREEN.  Remaining: E-0/E-1 (rung E statement + Ax2 probe
— the vacuity theorem IS most of the Ax2-need answer), W-1 (splice composition).

---

## Block 5 — E-0 EXECUTED: rung-E statement DRAFT + Ax2-need probe ANSWERED YES (lap 199b)

**File**: `wip/E0Ax2NeedProbe.lean` (src untouched; DRAFT marked DRAFT). Claims diff-verifiable.

1. **Ax2-need probe — YES, kernel-proven at the current `Nlog` gates.** `Zef2T` re-cloned
   post-swap (verbatim `Zef2` constructors + `trueRel`/`trueNrel`; `Zef2T.gate`, `Zef2T.ofZef2`
   proven). The concrete pair the order asked for: `zef2T_derives_paRefl` — the PA
   equality-axiom leaf `{∀x (x = x)}` closes in `Zef2T` at rank 0 (root ordinal 1, slot `·+1`,
   one `allω` + `trueRel` leaves); `zef2_not_derives_paRefl` — `Zef2` provably CANNOT (from
   lap-199's spine-head theorem via `zef2_rank0_singleton_underivable`: ANY singleton is
   uniform-spine, hence rank-0 underivable in `Zef2`). All standard triple. B(iii) confirmed
   per-leaf AND globally: **the rung-E embedding must target `Zef2T`**; adoption stays with the
   judge.
2. **Rung-E statement DRAFT** (`embedding_Zef2T_DRAFT`, typechecks, body `sorry`, wip-only):
   source `hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence`; budgets `∃ B d e` EXISTENTIAL and instance-uniform
   (W3 discipline); per-instance NF ordinal + operator inside `∀ m`; target `Zef2T` at slot
   `ewRootSlot e B`; `Γ_G` bound CONCRETELY to `{goodsteinBodyE/[nm m]}` with the faithfulness
   anchor `goodsteinSentence_eq_all_body : goodsteinSentence = ∀⁰ goodsteinBody` (`rfl`-grade,
   kernel-checked — no improvised translation). Flagged alternative for the ruling: hoist `∃ α`
   uniform (E–W Lemma 33).
3. **Consequence for the ruling**: with rung D vacuous over `Zef2` (block 4) and the leaves
   requiring (Ax2), the judged (Ax2) adoption now carries the WHOLE pipeline: on adoption,
   P/R read-off obligations re-home to `Zef2T` at the measured Stage-B costs (reduction
   mechanical, read-offs native re-proof — spine-head vacuity intentionally does not survive
   (Ax2)).

---

## Block 6 — E-1 first block: the CONNECTIVE-RULE GAP fires at statement level (lap 199c)

**File**: `wip/E0Ax2NeedProbe.lean` (§ E-1 seam probe; src untouched). Standard triple.

**Kernel fact**: `zef2T_not_derives_verum` — even WITH (Ax2), `Zef2T` cannot derive `{⊤}` at
rank 0 (`zef2T_rank0_noneSpine_underivable`, the none-spine invariant: (Ax2) only helps
literal heads; `⊤/⊥/⋏/⋎` remain ruleless).  The W3 case ladder's `verum`/`and`/`or` cases —
present in every PA-proof embedding, and covered in `Zekd` by `verumR`/`andI`/`orI` — have NO
counterpart in `Zef2`/`Zef2T`: the connective rules were dropped in the `Zef` port (sound for
cut-elim, where `erase_inert` shows they are never principal) and rung E now forces them back.

**Consequence (statement-level, judge-owned):** `embedding_Zef2T_DRAFT` is UNPROVABLE-AS-SHAPED;
the target calculus must be the FULL E–W Def-23 rule set `Zef2TC = Zef2T + verumR/andI/orI`
(`Zekd` shapes, `Nlog` gates).  Measured fallout to hand the ruling: `passAux` gains ⋏/⋎
PRINCIPAL cut shapes (the `erase_inert` dodge stops applying — E–W Lemma 25's finite arms,
mirror of the ∀/∃ shapes at fixed finite branching), read-offs gain two cases each.  The E-1
grind continues over `Zef2TC` (next block: clone + the leaf/EM cases against the amended
draft); the DRAFT text amendment itself is flagged for the judge, not self-ratified.

---

## Block 7 — E-1 block 2: `Zef2TC` erected + the budgeted EM PROVEN (lap 199d)

**File**: `wip/E1EmbeddingGrind.lean` (src untouched). Standard triple throughout.

1. **`Zef2TC`** — the amended target calculus (block-6 flag): `Zef2` verbatim + (Ax2)
   `trueRel`/`trueNrel` + the finite `verumR`/`andI`/`orI` (`Zekd` shapes, `Nlog` gates,
   `weak`-style NF/`Cl` side conditions; slot untouched — E–W relativizes only the ω-rule).
   `gate` + inclusion `Zef2TC.ofZef2` proven.
2. **`em_Zef2TC` — the budgeted excluded middle, SORRY-FREE** (the W3 `closed`-case engine =
   E–W Lemma 32's identity mechanism): any `Γ ∋ φ, ∼φ` is cut-free derivable at the
   DETERMINISTIC ordinal `ofNat (2·complexity+1)`, for every slot `f` monotone + inflationary
   with `clog (2·complexity+1) ≤ f 0`.  All hypotheses `rel1`-stable; ∀/∃ cases pair `allω`
   with `exI n` (bound `n ≤ f n` by inflationarity), finite cases ride `andI`/`orI`; ordinal
   ladder `ofNat` toolkit (`ofNat_lt_ofNat`, `Nlog_ofNat_le`, `clog_mono`) banked.  First
   nontrivial derivability content of the (Ax2)-extended calculus — the `closed` case of the
   W3 Derivation2 ladder is DONE modulo the value-congruence variant.
3. `embedding_Zef2TC_DRAFT` (typechecked, sorry) = the E-0 draft with the sole change
   `Zef2T → Zef2TC`.

**Next E-1 targets** (W3 ladder): `verum` (trivial now via `verumR`), `and`/`or` case lemmas
(budget-max bookkeeping), then the hard pair: `axm` (PA-axiom leaves via `trueRel` +
`em`-style Δ₀ verification — W1/W2 content) and `all` (ω-rule budget uniformity).

---

## Block 8 — E-1 block 3: the master predicate + case ladder, 7/10 cases SORRY-FREE; the `∃ K` statement amendment (lap 200)

**File**: `wip/E1EmbeddingGrind.lean` (src untouched). Build green (1342 jobs),
`blueprint_audit` ✓ 16, headline undrifted.

1. **STATEMENT DISCOVERY (amendment input, flagged for the judge — NOT self-ratified)**: the
   E-0/E-1 DRAFT's **fixed root slot cannot pay the `exI` gate**.  `Zef2TC.exI` demands the
   witness numeral `n ≤ f 0` with `f = ewRootSlot e B` structural (outside `∀ env`/`∀ m`),
   but the `Derivation2` `exs` witness value `(asg env) t` — and at the root the true
   goodstein witness `N(m)` — is assignment-dependent and unbounded.  The fixed-slot DRAFT is
   unprovable as stated.  Fix = the W3 `SomeK` witness-budget discipline transplanted to the
   slot: an **env-local relativization index `∃ K`** with slot `rel1 (ewRootSlot e B) K`
   (composes with the ω-rule via `rel1_rel1`, keeps `EwF1`/`EwF2` via `rel1_low` — pipeline
   undisturbed).  `embedding_Zef2TC_DRAFT2` = the so-amended rung-E statement (typechecked,
   sorry); DRAFT1 retained verbatim as judge input.
2. **`BudgetedEmbedsTC`** (the W3 master predicate over `Zef2TC`, amended shape):
   `∃ B d e (NF e), ∀ env, ∃ K α (NF α), Zef2TC α e ⊤ (rel1 (ewRootSlot e B) K) d (Γ.image (asg env ▹ ·))`
   with the operator fixed at the full closure `Cl ⊤` (every side condition `Cl.base trivial`).
3. **Monotonicity ports (all sorry-free)**: `Zef2TC.mono_f` / `mono_c` / `change_H` /
   `change_e` (the control ordinal is a phantom index of the derivation relation — proven by
   trivial induction; it acquires meaning only in the cut-elim pass).
4. **Slot/`Nlog` toolkit (all sorry-free)**: `Nlog_osucc_le` (mirror of `ewN_osucc_le`);
   `relSlot_le` (cross-`e` slot domination — `hardy_le_of_lt`'s `norm e₁ ≤ B` budget gate
   absorbed into the structural `B`); `relSlot_mono`; `relSlot_succ_gap` (one `K`-rung buys
   `+2` of root-gate slack — the `2·(x+…)` slot shape); `le_relSlot_zero`.
5. **The case ladder — SEVEN of ten `Derivation2` cases closed sorry-free** (standard triple,
   `#print axioms` anchors in-file): `closed` (consumes `em_Zef2TC'`; complexity is
   env-independent via `complexity_rew`), `verum`, `wk`, `shift` (assignment-collapse
   computation from `embedC` verbatim), `or` (osucc root + one `K`-rung), `and` and `cut`
   (two-premise joins: control tower `osucc (e₁+e₂)` — both strictly below, `norm eᵢ` into
   `B`; root `osucc (α₁+α₂)` — `Nlog_add_le_max_succ` absorbing + gate slack; budgets by
   `max`; cut rank `max (max d₁ d₂) (complexity+1)`, read gate paid via `B`).
6. **`budgetedEmbedding_Zef2TC`** — the master ladder ASSEMBLED by a real (non-sorry)
   induction; `sorryAx` enters exactly through the three disclosed hard leaves:
   **`axm`** (PA-axiom leaf = W1/W2 content: `trueRel`-driven bounded truth for 𝗣𝗔⁻,
   cut-tower for the induction schema), **`all`** (ω-rule: per-branch `(K_n, α_n)` must be
   uniformized — the `EmbeddingBound` uniform-ω-family port), **`exs`** (closed-term
   collapse: `asg env t` is closed but not a numeral — needs the `Zef2TC` (Ax2)-driven
   Leibniz kit; the witness VALUE is what forced the `∃ K` amendment).

**Next E-1 targets**: `exs` (closed-term collapse — likely the cheapest of the three;
`Zef2TC` equality congruence via `trueRel`, mirror `Provable.exI_closed`), then `all`
(uniform-ω-family), then `axm` (W1/W2 proper).
