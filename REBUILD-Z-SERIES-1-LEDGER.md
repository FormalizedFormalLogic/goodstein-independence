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

**NEXT (Stage-3 continuation):** the slot-composition lemma
`ewIter f α₀ (ewIter f α₁ m) ≤ ewIter f α m` for `α₀,α₁ < α`. Plan (via `ewIter_le_of_lt` +
`ewIter_lower` + `ewIter_monotone`): case on the ONote order of α₀,α₁; let δ = the larger (< α);
lift both iterates to δ by gated mono, giving `ewIter f δ (ewIter f δ m)`, then `ewIter_lower` at
δ < α. Gate bookkeeping: needs `ewN α₁ ≤ f(ewN δ + m)`, `ewN α₀ ≤ f(ewN δ + K)`,
`ewN δ ≤ f(ewN α + m)` — supplied by the pass invariant (the Zef2Prov gates). State with gates as
hypotheses (reusable), then wire into the pass induction. The slot side is NOT walled (gated
`ewIter` is ordinal-monotone) — no `EwF1`-of-`rel1` escalation needed for these containments.

**Gates**: build 🟢 1341 jobs · headline UNDRIFTED · both lemmas axiom-clean · no new axiom.
