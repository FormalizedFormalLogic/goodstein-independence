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
