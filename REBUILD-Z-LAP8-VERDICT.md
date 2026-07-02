# REBUILD-Z — LAP-8 VERDICT: the judged src port + ladder erection (2026-07-02)

> **For the judge.** Executes `REBUILD-Z-LAP8-ENTRANCE-2026-07-02.md`. Build 🟢 (`lake build`,
> 1341 jobs), headline `peano_not_proves_goodstein` UNDRIFTED
> (`[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]`), `blueprint_audit`
> PASSED (16 nodes), no new `axiom`, no `native_decide` in the ported `src`, wip `.lean` freeze
> untouched. **Two findings escalate (they are architect-owned, NOT self-ratified): a
> reduction-level gate-composition trap (P-d), and the L-E embedding trap-9 the entrance
> pre-authorized.**

## 1. Port deliverables — DONE

- **(P-a)** `src/GoodsteinPA/EwIter.lean` — verbatim port of the ratified lap-7 iterate (ewN,
  ewBall, `mem_ewBall_of_ewN_le`, EwF1/EwF2, ewStep/ewIter + unfold/zero,
  lower/infl/monotone/rel1_le, the lift + P1). P2/P3 native_decide probes stay in `wip` (src is
  anchor-free). Wired into `GoodsteinPABlueprint`.
- **(P-b)** `src/GoodsteinPA/OperatorZef2.lean` (new; `OperatorZeh` untouched) — `Zef2` +
  `mono_f`/`change_H`/`mono_Hf` + `Zef2Prov` + `ewRootSlot`(+`_f1`/`_f2`) + the C3 exit corollary,
  statements verbatim vs the wip freeze.
- **(P-c) — DISCHARGED by the forgetful map (mandated route).** `Zef2.toZef` (6-case induction,
  drops the gate) doubles as the conservativity witness. `readoff_sigma1_Zef2 := readoff_sigma1_Zef
  ∘ toZef` and `headline_readoff_Zef2 := headline_readoff_Zef ∘ toZef` — zero re-proof. Also banked
  `Zef2Prov.toZefProv`.
- **(P-e)** `cutElimPass_Zef2` pass pin (`sorry`, the laps-9+ gate) + `ewRootSlot` witnesses +
  `cutElimPass_exit_root_Zef2` (real derivation, sorryAx only via the pass pin).
- **(P-f)** Supersession is docstring-only; old `Zef`/`iterSlot`/old pin 3 statement tokens in
  `OperatorZeh.lean` untouched.

## 2. Pins 1–2 over `Zef2` (P-d) — one DISCHARGED, one obstruction ESCALATED

- **`allInv_Zef2` — DISCHARGED (real proof).** Inversion leaves ordinals unchanged, so each rebuilt
  node's gate transports from its input gate to the relativized slot `rel1 f n₀` via `gate_rel1`
  (`f` monotone); branch gates ride the new `Zef2.gate` projection (every constructor exposes
  `ewN α ≤ f 0`) + `rel1` monotonicity. The inversion suite's other members (`orInv`/`andInvL`/
  `andInvR`) are propositional and route the same way when needed downstream.
- **ewN arithmetic — BANKED (kernel-verified).** `ewN_addAux_le`, `ewN_add_le` (unconditional
  sub-additivity), `ewN_osucc_le` (NF, grows by ≤1), composite `ewN_osucc_add_le`:
  `ewN (osucc (α + γ)) ≤ ewN α + ewN γ + 1`.
- **`cutReduceAllAuxRunning_Zf2` / `stepAllω_Zf2` — DISCLOSED sub-pins; GATE-COMPOSITION
  obstruction (candidate reduction-level trap; architect-owned).** The reduction's synthesized
  `allω`/`cut`/`exI` roots sit at `osucc (α + γ)`; over `Zef2` each needs a gate
  `ewN (osucc (α + γ)) ≤ (g ∘ f) 0 = g (f 0)`. By `ewN_osucc_add_le` this reduces to
  `ewN α + ewN γ + 1 ≤ g (f 0)`. The gates the derivation actually carries are
  `ewN γ ≤ f 0` (the node's own gate, ∃-side base slot `f`) and `ewN α ≤ g 0` (the ∀-family gate
  from `fam`, ∀-side base slot `g`). With `EwF1 g` (`g (f 0) ≥ 2·f 0 + 1`) the bound closes **iff
  `ewN α ≤ f 0`** — the ∀-family ordinal must be gated at the **∃-side** base. But `fam`'s gate is
  at the ∀-side base `g`, and `ewN` is **not** ordinal-monotone (the trap-8 pathology), so no
  `α' ≤ …` witness slack recovers it. The cross-slot gate `ewN α ≤ f 0` is neither derivable nor an
  `f.1`-class hypothesis; baking it in would be a statement change → escalation. Its resolution is
  entangled with how the FORBIDDEN `cutElimPass_Zef2` wires the two premise slots (are both
  dominated by a common base after the rank IH?), which is why it is architect-owned. **This is the
  precise, kernel-grounded reason pins 1–2 do not re-thread over `Zef2` as-stated.**

## 3. Ladder erection (L-items) — four rungs erected, one trap-9 flagged

**Representation finding (binding gate interaction).** `BlueprintAudit.categoryOfFootprint`
computes `broken` for ANY `sorryAx` footprint, and `reconcile` fails `broken` regardless of the
claimed category. A new `axiom` is FORBIDDEN this lap. Therefore sorry-bearing rung pins **cannot**
carry `@[goodstein_blueprint]` machine attributes (they would fail the audit) and cannot be
promoted to axioms. The rungs are erected as disclosed `sorry` theorems (raising the src count IS
the decomposition) and live on the **tex dep-graph** (`thm:zeh_rank_zero`/`thm:zeh_embedding`/
`thm:wainer_splice`); ledger metadata is carried in each docstring, and ledger-14 (`wainer_axiom`)
now cites the rungs. The entrance's "attributes 17+" is incompatible with the audit's
broken-on-sorry rule + the no-axiom gate; the tex dep-graph is the faithful representation.

- **L-R `rankToZero_Zef2` — FAITHFUL/CONCRETE** (pure `Zef2` vocabulary): iterate
  `cutElimPass_Zef2` down the cut rank `d → 0`; ordinal tower `collapseIter` (**NF preservation
  `collapseIter_NF` PROVEN — real content**), slot tower `ewIterTower`. Ledger: debt, "1", 90.
- **L-D `readoff_delta0_Zef2`** — the Δ₀ bounded-∀ matrix read-off (Towsner §5.4), re-homed to
  `Zef2`; parametric over the bounded-truth predicate `matrixTrue` (concrete Δ₀ evaluator at
  discharge). Ledger: debt, "2-3", 80.
- **L-E `embedding_Zef2` — ESCALATED (trap-9, architect-owned, entrance-pre-authorized).** Stated
  per the JUDGE AMENDMENTS: (i) existential budget `∃ B`; (ii) `ewRootSlot`-class slot. A FAITHFUL
  statement must bind the target sequent `Γ_G` to the concrete `𝗣𝗔`-goodstein translation and
  hypothesize `𝗣𝗔 ⊢ ↑goodsteinSentence` (the PA-proof source). That translation apparatus is not
  available at `Zef2`-statement level this lap (it lives in `Statement`/`WainerRoute` and would
  cross-import). Per the entrance's "escalate rather than improvise there," the rung is stated
  **parametrically over `Γ_G`** with the judge's existential-budget + `ewRootSlot` shape; binding
  `Γ_G` to the PA translation is the escalation locus. Ledger: debt, "8-20", 65.
- **L-W `wainer_splice_Zef2`** — the splice (E→R→D + Hardy Lemma-19 brackets vs the banked lower
  bound `goodsteinLength_dominates_fastGrowing`), parametric over the external growth binding (the
  concrete `goodsteinLength`/`goodsteinSentence` lives in `WainerRoute` and would cross-import).
  Ledger: debt, "2-4", 75.

## 4. Gates (all met)

Build 🟢 1341 · headline UNDRIFTED · `src` sorry delta = EXACTLY the named pins (old pin 3
`cutElimPass_Zf` unchanged + `cutElimPass_Zef2` pass-pin + P-d `cutReduceAllAuxRunning_Zf2`/
`stepAllω_Zf2` + rungs `rankToZero_Zef2`/`readoff_delta0_Zef2`/`embedding_Zef2`/
`wainer_splice_Zef2`; `allInv_Zef2` + both read-off pins DISCHARGED, not sorries) ·
`blueprint_audit` PASSED · NO new `axiom` · NO `native_decide` in ported `src` · wip `.lean` freeze
byte-identical.

## 5. For the judge — decisions requested

1. **The reduction gate-composition trap (§2).** Is the cross-slot gate `ewN α ≤ f 0` an admissible
   `f.1`-class-adjacent hypothesis (making pins 1–2 dischargeable as-scoped), or does it force a
   `Zef2`-level or slot-composition redesign? Its answer is entangled with the pass's slot wiring.
2. **L-E trap-9 (§3).** Ratify the parametric `embedding_Zef2` shape, or supply the concrete
   `𝗣𝗔`-goodstein → `Zef2`-sequent translation target (the cross-module binding) so the rung can be
   stated faithfully non-parametrically.
3. **Ladder representation (§3).** Confirm the tex-dep-graph representation of the sorry rungs
   (machine `@[goodstein_blueprint]` rows being impossible without an axiom).

**STOP for the judge.**
