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

## What's happened (newest first)
- **2026-06-22 (lap 6 — review):** Verified build green (1257 jobs); **M6 lower-bound half DONE** —
  promoted `wip/LowerBoundHardy.lean → src/GoodsteinPA/LowerBound.lean`. `lowerBound_hardy_selfcontained`
  is the full Towsner Thm 17.1, `Hdom` discharged via the ported domination chain (`+2`→strict iterate
  split). `#print axioms` = trust base + documented `native_decide` Goodstein base-case artifacts (🟢).
  Re-grounded the remaining direction against the ANALYSIS doc's 5-step spine: the crux is now the
  **witness-bounded calculus `Zᵏ` over real syntax + embedding + cut-elim-with-`k` + subformula bridge**,
  with the **opaque-Σ₁ language gap (M7a)** flagged as the other hard piece.
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
1. **`Zᵏ` — witness-bounded ω-calculus over real `ℒₒᵣ` syntax** (Towsner §15). `src/Zinfty.lean`'s
   `Deriv` + a **truth-atom rule** (`τ α < k`) + a **witness bound on `∃`** (`v ≤ h_α(k)`). The keystone
   the embedding lands in and cut-elim operates on. **NEXT — start the definition + structural lemmas.**
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
