# STATUS — GoodsteinPA 📊

**Kirby–Paris: `𝗣𝗔 ⊬ Goodstein`, via Towsner's Route B (witness-bounded `Z_∞` ω-rule calculus + ε₀
cut-elimination + Hardy lower bound).** · **Build**: 🟢 green (1257 jobs, `lake build GoodsteinPA`)
· **Updated**: lap 6 · 2026-06-22 · `2e7ba5c`

## Where it stands
Two of the three Phase-2 girders are **machine-checked and `#print axioms`-clean**: the ε₀
cut-elimination for the infinitary calculus (M5, `src/Zinfty.lean`) and — **as of lap 6** — the
**full cut-free Hardy lower bound, Towsner Thm 17.1, with no hypotheses beyond `α.NF`** (M6,
`src/LowerBound.lean`: `lowerBound_hardy_selfcontained`). Phase 0 (encoding + faithfulness bridge,
M1) and Phase 1 (Gödel II hook, M2) are landed and clean. The headline
`Statement.peano_not_proves_goodstein` is **still a literal `sorry`** (anti-fraud — correct): the
two completed girders are over *different* calculi (M5 unbounded `(α,c)` over real `ℒₒᵣ` syntax; M6
witness-bounded `(α,k)` over the `GForm` fragment) and are **not yet unified**. The remaining work is
the connecting spine — see Outstanding.

## Route decision (lap 7) — STAY ON ROUTE B (Towsner)
The operator delegated Route A vs B to the box (`archive/findings/…operator-route-choice.md`). **Decision:
Route B.** Rationale: (1) the one genuinely-doubtful Route-B girder — the `(α,k)` cut-elimination
`k`/`τ` bookkeeping — was the reason to hesitate, and **lap 7 resolved it** (it is not a wall; `k`
simply grows and the lower bound holds for all `k` — see `ANALYSIS-2026-06-22-cutelim-k-threading.md`).
(2) M5+M6 are both Route-B assets already banked. (3) The remaining Route-B risk is M4 (embedding) +
M7a (the PA↔PA⁺ arithmetization bridge); Route A trades those for the full Gentzen `TI(ε₀)⊢Con(PA)` +
`Goodstein⟹TI(ε₀)` + the `PA_delta1Definable` Foundation axiom — a *larger* unproven surface, not
smaller. Revisit only if M7a proves intractable after sustained effort.

## What's happened (newest first)
- **2026-06-22 (lap 7, cont. — §19.6 norm ingredient PROVED; commuting-case frontier mapped):**
  Proved `norm_addAux_le` and `norm_add_le {α γ NF} : norm(α+γ) ≤ norm α + norm γ` (axiom-clean; the
  `τ(α#β)≤τα+τβ` budget fact; NF essential — NF-free version machine-checked FALSE, eq-merge killed by
  additive-principality absorption). `wip/BoundedZinfty.lean` now **sorry-free**. Then, starting
  `cutReduceAll`, **uncovered a genuine §19.6 obstruction**: the `allω`-commuting case cannot preserve
  the ω-rule's `max{k,n}` norm budget after adding `α` to the bound (`norm(α+βₙ)~norm α+n > max K n` for
  large `n`). Towsner's "follows from IH" glosses this; the fix needs Buchholz operator-control or a
  controlled `Zk.allω` index. Precisely characterized + 3 attack options in
  `ANALYSIS-2026-06-22-cutelim-k-threading.md` ADDENDUM; `ON-LINE-REQUEST` re-filed (one layer down).
- **2026-06-22 (lap 7 — cut-elim `k`/`τ` crux RESOLVED, offline):** Read Towsner §15–§20 on disk and
  answered the open `ON-LINE-REQUEST` directly. **Finding:** the lap-6 "norm grows under addition so
  cut-elim might break `norm<k`" worry was a misframing. (a) `k` is **not** fixed — it grows (§19.5
  `k↦2k`; §19.6 `k↦h_{β#ω}(k)`; §19.7 `k↦h_{ω^α}(k)`), engineered to absorb `τ(α#β)≤τ(α)+τ(β)`.
  (b) The lower bound `lowerBound_hardy_selfcontained` is already `∀k`, so growth is harmless.
  (c) Every `ONote` is `<ε₀` by construction, so the ε₀ side-condition is **free**. ⟹ state the whole
  cut-elim chain **existentially in `k`** (`CutFree α Γ := ∃k, Zk α k 0 Γ`); ordinary `+` with slack
  suffices (no `nadd` needed). `ON-LINE-REQUEST` closed; route chosen (B). See
  `ANALYSIS-2026-06-22-cutelim-k-threading.md`. **§19.6/§19.7 port now unblocked.**
- **2026-06-22 (lap 6 — review + build-out):** **M6 lower-bound half DONE** — promoted
  `wip/LowerBoundHardy.lean → src/GoodsteinPA/LowerBound.lean`; `lowerBound_hardy_selfcontained` =
  full Towsner Thm 17.1, only `α.NF` (axioms = trust base + 🟢 `native_decide` base cases). Then
  **built the step-1 keystone** `wip/BoundedZinfty.lean`: the **witness-bounded calculus `Zᵏ` over real
  `SyntacticFormula ℒₒᵣ`** (ONote-indexed, B-style, with the truth rule `τ α<k` + `∃`-witness bound
  `v≤h_α(k)` + cut) and its whole §19.2–19.5 cut-elim front: `mono_k`/`mono_c`/`wk`/`weakening`, the
  **full inversion suite** (∨, ∧-L/R, ∀ — all axiom-clean), and the **§19.5 ∧/∨ cut-reductions**
  (`cutReduceConj`/`Disj`, axiom-clean). **Finding:** the `ω^α` blow-up preserves the `norm<k` budget
  (`norm(ω^α)=max(norm α,1)`, machine-checked) but ordinal *addition* bumps it (`norm(ω+ω)=2`) — so
  §19.6's bound bookkeeping needs care (filed `ON-LINE-REQUEST.md` for Towsner's precise `τ`/`k`
  threading). Remaining: §19.6 (∀/∃ reduction) + `cutElimStep`/`cutElim`, then M4 + M7.
- **2026-06-22 (lap 5):** RESOLVED the gAll/I∀ lower-bound frontier (the lap-4 wall), machine-checked.
  Ported the Hardy hierarchy → `src/Hardy.lean` (`hardy`/`norm` = Towsner `h_α`/`τ`); built the
  witness-bounded calculus `B` over `ONote` with the **concrete** Hardy data; proved
  `lowerBound_existential_hardy` (∀-free, zero abstract hyps), `B.allInv` (∀-inversion), and
  `lowerBound_hardy` (full Thm 17.1 mod `Hdom`). Resolution = **invert `gAll` away, don't accumulate**
  (a set-sequent `gAll` lets the ω-rule re-expand at a reachable index & `trueR`-close). Ported the
  Goodstein-dominates-fastGrowing chain → `src/Domination.lean`. (`ANALYSIS-2026-06-22-bounding-resolution.md`.)
- **2026-06-22 (lap 4):** Ground-truthed Towsner §10–§19 vs the Lean. Found + machine-checked
  (`wip/WitnessBound.lean`) the **witness-bound gap**: the M5 `(α,c)` cut-elim is OFF the headline path
  (unbounded `∃` ⇒ lower bound false for it). Built the corrected witness-bounded calculus, proved the
  ∃-fragment lower bound, proved the unbounded calculus collapses (`unbounded_proves_goodstein`).
- **2026-06-22 (lap 3):** Proved the ENTIRE Z_∞ cut-elimination (Towsner §19), zero sorries,
  axiom-clean: inversions + cut reductions §19.5 (∧/∨) & §19.6 (∀/∃) + `cutElimStep` §19.7 + `cutElim`
  §19.9. `Ordinal.nadd` ABSENT in mathlib v4.31.0 → ordinary `+` with `+1` slack (additive principality
  of `ω^c`). Promoted `wip/ZinftyF.lean → src/GoodsteinPA/Zinfty.lean`. (M5 ✅)
- **2026-06-22 (lap 2):** Built the real `Z_∞` calculus over Foundation's `SyntacticFormula ℒₒᵣ` with
  set sequents; proved all three inversion lemmas (§19.2–19.4); reduced cut-elim to `cutElimStep`.
- **2026-06-22 (lap 1):** M1 (`goodsteinTerminates_re`, Phase 0 axiom-clean), M2 (`Reduction.lean`
  Gödel II hook), Phase-2 decomposition doc (Towsner-grounded ladder).

## Outstanding
The lower-bound side (M6) and the cut-elim engine (M5) are done but disconnected. The remaining spine
(ANALYSIS doc §"M4 scoping", the 5 steps) connects them and reaches the headline:

### Short-term (mirror PENDING_WORK top) — the connecting spine, hardest-first
1. **`Zᵏ` — witness-bounded ω-calculus over real `ℒₒᵣ` syntax** (Towsner §15). **DEFINED + §19.2–19.5
   DONE** (`wip/BoundedZinfty.lean`): calculus + `mono_k`/`mono_c`/`wk`/`weakening` + inversions
   (∨,∧,∀) + ∧/∨ cut-reductions, all axiom-clean. **NEXT — §19.6** (∀/∃ cut-reduction; bound framing
   `α + γ` via `ONote.add`, witness-cut in the principal `exI` case) then `cutElimStep` (`ω^α` blow-up;
   needs the `norm(ω^α)`/`norm(α+γ)`/`norm(osucc)` budget-preservation lemmas) + `cutElim`.
2. **M4 — embedding `PA ⊢ φ ⟹ Zᵏ ⊢^{α,k}_c φ`** (α<ε₀, finite c), Towsner §16/§18. Reuse Foundation's
   finitary `Derivation`; map rules across, `∀`→ω-rule; finite induction instances ⟹ finite cut rank.
3. **Cut-elim with `k`** — redo `src/Zinfty.lean` §19 tracking the bound (`h_{ω^α}(k)`; ε₀ closed under
   `ω^·` ⇒ the bound survives). Strategy ports; only the bound bookkeeping changes.
4. **Subformula bridge** — a *cut-free* `Zᵏ`-derivation of `{gAll}` has only subformulas of `gAll` =
   the `GForm` fragment (substitution-closure), so it **is** a `B`-derivation ⇒ contradicts
   `lowerBound_hardy_selfcontained` (M6, **done**). The clean small connector.

### Long-term
- **M7a — the language gap (Towsner Remark 10.3).** Our headline is real-`ℒₒᵣ` PA with an **opaque Σ₁**
  `goodsteinSentence = ∀⁰ (codeOfREPred goodsteinTerminates)`, not the transparent `∀x∃y g_y(x)=0` the
  calculus/subformula-bridge needs. Build a transparent Π₂ `gAllReal` (arithmetize `goodsteinSeq` as a
  real formula) + `𝗣𝗔 ⊢ goodsteinSentence ↔ gAllReal` (gated by `Bridge.lean`'s spec so faithfulness
  can't regress). The other genuinely-hard girder besides M4.
- **M7b — assembly:** chain embed ⟹ cut-elim ⟹ subformula-bridge ⟹ contradiction ⟹ discharge the
  headline `sorry`. (Route A via `Con(PA)` + `goodstein_implies_consistency` stays as the documented
  alternative; it would re-introduce `PA_delta1Definable`.)

### To completion
Headline discharged ⟺ steps 1–4 + M7a + M7b land AND `#print axioms peano_not_proves_goodstein` is
`[propext, Classical.choice, Quot.sound]` (+ the documented `native_decide` Goodstein base-cases from
the domination path — 🟢 finite witnesses; no `PA_delta1Definable` on Route B).

## Axiom ledger (per headline / landmark theorem — the fidelity spine)
| theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `peano_not_proves_goodstein` (headline) | uncond. (Kirby–Paris) | `propext, sorryAx, choice, Quot.sound` | 🔓 open `sorry` — steps 1–4 + M7 remain; **0** real math axioms |
| `goodsteinSentence_faithful` (bridge) | encoding correctness | `propext, choice, Quot.sound` | 🟢 clean (trust base) |
| `goodsteinTerminates_re` (M1) | r.e. of termination | `propext, choice, Quot.sound` | 🟢 clean |
| `Deriv.Provable.cutElim` (M5, §19.9) | ε₀ cut-elimination | `propext, choice, Quot.sound` | 🟢 clean — over real `ℒₒᵣ`, unbounded `(α,c)` (needs `k` retrofit for the headline path) |
| `hardy_le_of_lt` (M6, `src/Hardy`) | Hardy index monotonicity (Hmono) | `propext, choice, Quot.sound` | 🟢 clean |
| `lowerBound_existential_hardy` (M6) | ∃-fragment 17.1, concrete Hardy/`G` | `propext, choice, Quot.sound` | 🟢 clean — zero abstract hyps |
| `B.allInv` (M6) | ∀-inversion (I∀-frontier resolution) | `propext, choice, Quot.sound` | 🟢 clean |
| `lowerBound_hardy` (M6) | full Thm 17.1 mod `Hdom` | `propext, choice, Quot.sound` | 🟢 clean |
| `lowerBound_hardy_selfcontained` (M6, **lap 6**) | **full Thm 17.1, only `α.NF`** | `propext, choice, Quot.sound` + 12 `native_decide` base-case `ax_*` | 🟢 clean — the `ax_*` are 🟢 finite Goodstein base-case witnesses (acceptable indefinitely) |
| `not_proves_of_implies_consistency` (Route A) | meta-reduction | `…, PA_delta1Definable` | 🟡 Foundation axiom; **Route A only** — Route B avoids it |

Math-axiom count on the (eventual) Route-B headline target: **0** beyond the trust base + the 🟢
`native_decide` Goodstein base-case witnesses on the domination path. The `sorryAx` on the headline is
the honest open marker. `PA_delta1Definable` (🟡) sits only under the unused Route-A hook.

## Pointers
ROADMAP/plan: `EXPEDITION-PLAN.md`, `PHASE2-DECOMPOSITION.md` · architecture: `ANALYSIS-2026-06-22-bounding-resolution.md`
· newest baton: `HANDOFF-2026-06-22-lap6.md` · open-items: `PENDING_WORK.md` · charter: `DIRECTION.md`
