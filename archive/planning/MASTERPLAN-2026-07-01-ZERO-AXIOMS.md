# MASTERPLAN — full discharge to `[propext, Classical.choice, Quot.sound]` (2026-07-01)

> **Authored host-side (Ren, Fable-5 deep-dive) at the operator's direct request**: *"make a solid plan to
> formalize the goodstein independence completely, down to the base 3 axioms."* This is the
> human-architect plan `EXPEDITION-PLAN.md` says Phase 2 requires. It is the proposed successor to the
> lap-171 directive; the route-language change in §3 needs **operator ratification** before the fleet
> acts on it (it touches a FORBIDDEN line the operator set on 2026-07-01).

---

## 0. Verdict

**Commit. There is a real, phased path to zero custom axioms — do not abandon.**

The scope-reality doc is right that the ε₀ girder is the whole remaining deliverable, but it undersells
the repo's own position: **a large fraction of the monument is already built and axiom-clean in this
repo** — the full unbounded `Z∞` ω-rule cut-elimination (M5, *never done in Lean anywhere else*), the
complete unbounded embedding `𝗣𝗔 ↪ Z∞` (M4), the witness-bounded operator calculus with every local
hard case probed, the entire lower-bound half (Towsner Thm 17.1, self-contained), and the assembly
skeletons on three spines. What remains is: **one engine** (witness-bounded embedding + operator
cut-elimination + Σ₁ read-off), built as **five phases** on machinery that is 60–70% banked, with the
two genuinely-hard bets (bounded induction/EM, operator cut-elim's control-raising) explicitly gated.

- Estimated remaining: **~30–60 grind laps + 6–8 architect/judge sessions ≈ 2–4 calendar months** at
  recent cadence (laps 132→171 ran ~4.4/day).
- Confidence: engine completes on this architecture **~55–65%**; with one architecture fallback
  (Buchholz fully-operator-controlled derivations) **~70–75%**. Honest, not optimistic — see §8.
- The result would be **the first formalized concrete PA-independence in any proof assistant**
  (landscape verified 2026-07-01: `ON-LINE-FINDINGS-2026-07-01-independence-formalization-landscape.md`).

## 1. Ground truth (verified in-kernel this session — real `#print axioms`, not docstring trust)

**Banked assets (all `[propext, Classical.choice, Quot.sound]` unless noted):**

| Asset | Where | Note |
|---|---|---|
| `goodsteinSentence` faithful encoding + ℕ-truth bridge | `Encoding`/`Bridge` | LOCKED trust surface |
| `goodstein_terminates_engine : ∀ m, ∃ N, goodsteinSeq m N = 0` | `Domination:389` | feeds the ¬-half of full independence (§W6) |
| **Lower bound** `lowerBound_hardy_selfcontained` (full Towsner Thm 17.1, hypotheses = `α.NF` only) | `LowerBound:362` | ✅ verified: 3 canonical + the 12 documented `native_decide` base facts |
| `cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing` | `WainerRoute` | ✅ verified: same base |
| **`Z∞` calculus + FULL cut-elimination** (§19.2–19.9: inversions, cut reductions, `cutElimStep`, `cutElim`) | `Zinfty`/`ZinftyGen` | M5 — unbounded; the structural template for W4 |
| **Embedding `embedC : Derivation2 (𝗣𝗔) Γ → … Provable α c (image Γ)`** | `Embedding` | M4 — unbounded; the structural template for W3; all Derivation2 cases handled once |
| ε₀-bound-tracking embedding discipline (`PXFcFin`/`PXFcLt`, uniform ω-families, `provable_em_x_bdd ≤ 2·complexity`) | `EmbeddingBound` | the `< ε₀` half of W3's design, already invented |
| **Operator calculus `Zekd`** (witness bound `n ≤ hardy e (k+d)`) + `ZekdSomeK` surface: structural layer, inversions, `cutReduceConj/Disj/AllAux(+_control)`, `ZekdBoundedTruth`/`ofBoundedTruth`, closed-term `exI`, the `valueCongruent*` EM family, **induction-leaf cut-tower + running-index probes** | `OperatorZinfty` | the substrate of W1–W4 |
| `inductionLeaf_runningIndex_witnessBound` (:1033) + `…_fixedIndex_…_impossible` (:1025) | `OperatorZinfty` | machine-validated design decision: the ω-rule premise at index `max k n` pays the witness budget — **the exact wall Route A died on, already solved here at the leaf** |
| Hardy infrastructure (`hardy_add_collapse`, `hardy_le_of_lt`, `hardy_le_fastGrowing`, norm bookkeeping) | `Hardy`, `OperatorZinfty` | control-ordinal raising + the fastGrowing conversion for §W6 |
| Gödel-II wiring (`peano_not_proves_consistency`, contraposition) | `Reduction` | Route A leftover, stays banked |

**Debts (custom axioms live anywhere on a spine):**

| Debt | Spine | Disposition under this plan |
|---|---|---|
| `goodstein_implies_consistency` | A (Gentzen→Gödel II) | **retire with Route A** (banked, off the headline at W6) |
| `wainer_bound_of_pa_proves_goodstein` | B-Wainer | **discharged `axiom → theorem` at W6** as a read-off corollary of the engine |
| `pathB_*_capstone` ×7 | B-Towsner ledger | **reified (W0), then discharged (W1–W5)** — this IS the work |
| 12 × `Dom.goodsteinLength_base_cases._native.native_decide.*` | lower bound | **burn down at W7** (fallback: keep as the operator-blessed documented base) |

## 2. The architectural defect to fix first: the capstone ledger is nominal, not logical

The 6 middle Path-B markers (`RouteBPeanoMinusAxiomLeaves` … `RouteBSubformulaProjection`) are **empty
inductive `Prop`s** parameterized by `hpa`. Consequence (judge lap-171 §2 flagged it; confirmed here):
each capstone axiom is **logically equivalent to the entire headline** — an empty Prop can only be
inhabited from `hpa` if `hpa` is refutable, so no capstone is individually dischargeable, and a
"discharge" of any single one would have to smuggle the whole theorem. The ledger currently tracks
*names and evidence*, not decomposed mathematical content. `blueprint_audit` cannot see this (it audits
category-vs-footprint, not statement strength).

**Fix (W0): reify every marker as the real theorem statement it stands for.** Then each capstone is
independently provable, a fraudulent discharge is impossible by construction, and the stage-chain
composition *literally is* `RouteBBridgeFromPAProof`. The audit/allowlist discipline carries over
unchanged. The reified statements are the new **trust surface** — statement-audited against Towsner
§15–19 + Buchholz–Wainer 1987 (both on disk), same LOCK discipline as `Defs`/`Bridge`.

## 3. Route unification (the strategic correction — needs operator ratification)

The lap-171 decision language ("PIVOT-B = Wainer, **not** the Towsner operator lane"; FORBIDDEN:
"Towsner/A' capstones as the mainline") contains a false dichotomy that dissolved the same day it was
written: the Buchholz–Wainer paper (sourced 2026-07-01, after the judge review whose table line
"Wainer: *no cut-elim*" it corrects) proves the classification's load-bearing direction **by ω-rule
embedding + cut-elimination** — i.e., by exactly the machinery of the `OperatorZinfty` lane. There is
one engine; "Wainer" and "Towsner §17.1" are two read-offs from its output:

- **Towsner read-off** (strictly less work): the PA proof of `γ` runs through the engine directly and
  dies against the banked `¬ B` lower bound. No `ProvablyTotal` interface, no Kleene coding, no
  provable-totality bridge — the general classification is never needed for the headline.
- **Wainer read-off** (the operator's named objective): the same cut-free output yields
  `goodsteinLength m ≤ hardy e (k+m)` for all `m`, and `hardy_le_fastGrowing` + successor-level
  absorption converts to `EventuallyLE goodsteinLength (fastGrowing o)` — discharging
  `wainer_bound_of_pa_proves_goodstein` **verbatim, `axiom → theorem`**.

**Proposed directive change** (one sentence, for the operator to ratify into `DIRECTION.md`):

> The `OperatorZinfty`/`someK` witness-bounded machinery **is the discharge substrate for the Wainer
> debt** (it is how Buchholz–Wainer themselves prove it); the lap-171 FORBIDDEN line applies to Route A
> (internal-Z / `Crux2Blueprint` / M2) only. Mainline = the reified capstone ladder (§4); both
> read-offs ship at W6.

Everything else in the 2026-07-01 operator decision stands unchanged: **full discharge or abandon**;
a named axiom is a live audit surface for a debt being paid, never the ship.

## 4. The engine, reified (the new capstone statements — sketches, finalized at W0)

Working over `Seq := Finset (SyntacticFormula ℒₒᵣ)`, numeral assignment `asg e` closing all free
variables (as in `embedC`), `ZekdSomeK α e d c Γ := ∃ K, ZekdProv α e K d c Γ`:

1. **`boundedAxiomLeaves`** — for every `σ` in the finite `𝗣𝗔⁻` + equality-axiom inventory and every
   assignment: `∃ (finite α) e d, ZekdSomeK α e d 0 {image σ}`, budgets a function of `σ` only.
2. **`boundedInduction`** — for every induction instance `ind ψ` (arbitrary matrix `ψ`!) and every
   assignment: `∃ α ≤ ω·2ish, e, d, c ≤ f(complexity ψ), ZekdSomeK α e d c {image (ind ψ)}` — via the
   bounded-EM complexity recursion + the running-index ω-rule cut-tower (probes banked).
3. **`budgetedEmbedding`** (master, subsumes old capstones 4+5) —
   `Derivation2 (𝗣𝗔 : Schema) Γ → ∀ asg, ∃ α < ε₀ (NF), e, d, c, ZekdSomeK α e d c (image Γ)` —
   one induction over `Derivation2`, `embedC`'s 10 cases as the template, `EmbeddingBound`'s
   uniform-family discipline for the `< ε₀` bound.
4. **`operatorCutElim`** — `ZekdSomeK α e d c Γ → NF-data → ZekdSomeK (ωTower c α) (econtrol c e α) d 0 Γ`
   (rank `c → 0`, ordinal exponentiated, control ordinal raised; both explicit and `< ε₀`).
5. **`sigma1Readoff` / `fragmentProjection`** — a cut-free `ZekdSomeK` derivation of `{image γ}`
   projects to `∃ α k, B α k {gAll}` (Towsner §17.1 shape), collapsing the Σ₁ run-matrix
   sub-derivations by decidable ℕ-truth.
6. **Assembly** — 5∘4∘3 gives `RouteBBridgeFromPAProof`; `peano_not_proves_goodstein_of_routeBBridge`
   (already proven) closes the headline against `no_routeBCapstone` (already proven).

## 5. Phases

**W0 — Re-architecture (host/architect + judge, 1–2 sessions; NOT treadmill work)**
Reify the capstones per §4 (statement-audit against the sources = the critical human step); rewire
`PathBProbe`'s ledger + `blueprint_audit` + `lean-axiom-gate` allowlist onto them; **prune the default
build** — move the frozen Route-A mass (`InternalZ` 10.4k, `Crux2Blueprint` 5.5k, `Zsubst` 3.9k, the
`Internal*`/descent files ≈ 25k lines) to a `GoodsteinPABanked` lib target off the per-lap gate (CI
builds it weekly; every future lap gets minutes faster). Update `DIRECTION.md` (post-ratification).
*Gate: audit green over reified nodes; headline still assembles.*

**W1 — Bounded axiom leaves (reified #1). Est 1–2 laps · 80%.**
Finite inventory case-split; `ZekdBoundedTruth`/`ofBoundedTruth` banked; `addEqOfLt` is the lone
existential-witness case (closed-term `exI` probes banked).

**W2 — Bounded induction (reified #2). Est 4–8 laps · 65%. Coupled hard bet #1.**
Banked: the cut-tower probes, the running-index theorems, the `valueCongruent*` EM family for
atoms/⋏/⋎/QFree. Remaining: the **bounded EM recursion for arbitrary `ψ`** (mirror
`provable_em_x_bdd`'s constant-family trick, with witnesses riding the running index) and the shell
assembly discharging the probes' explicit premises. *This phase must DROP the explicit-hypothesis
probes into hypothesis-free theorems — the W2 exit gate.*

**W3 — Global budgeted embedding (reified #3). Est 6–13 laps · 60%.**
Judge-confirmed un-started globally, but `embedC` enumerates every case and each non-structural case
has a someK probe. **Mandated first move: a 1-lap statement spike** — the master theorem + every
rule-case obligation as named `sorry`s, so any rule that structurally cannot carry a budget surfaces
immediately. **Abort trigger T-W3 (pre-registered):** such a rule found and un-designable after 3
further laps → HALT, escalate to operator (fallback: Buchholz operator-controlled derivations `Zᵉ`,
the literature's exact tool — a re-design, not a dead end).

**W4 — Operator cut-elimination (reified #4). Est 5–10 laps · 60%. Coupled hard bet #2.**
The unbounded `cutElim` is a complete structural template; `cutReduce*` + `_control` + norm/Hardy
bookkeeping banked. The isolated genuinely-new piece: **the running-index operator-control replacement**
in the global rank-lowering recursion (the ∀/∃ principal cut whose ∃-witness bound must be absorbed by
raising `e`; Towsner §19.6 / Buchholz's operator step; `hardy_add_collapse` exists for the nesting).
Design-spike-first, same discipline. **Abort trigger T-W4:** 2× estimate (20 laps) without the master
recursion closing → HALT, escalate.

**W5 — Σ₁ read-off / fragment projection (reified #5). Est 5–11 laps · 70%.**
"Adapters into an already-proven theorem" (judge). Named subtlety: `γ`'s matrix is a **Σ₁ run formula**
(nested ∃ from sequence coding), not an atom — the projection collapses matrix sub-derivations via
decidable `atomTrue` truth + someK inversions (banked) + a false-side-formula elimination lemma
(Towsner §17.1's treatment). Output lands exactly on `LowerBoundHardy.B`.

**W6 — Assembly, corollaries, full independence. Est 1–2 laps · 90%.**
- Chain W1–W5 ⇒ headline; **re-point `Statement.peano_not_proves_goodstein` at the engine**; retire
  `goodstein_implies_consistency` + Route A wiring to the banked lib.
- **Discharge `wainer_bound_of_pa_proves_goodstein` `axiom → theorem`** (the Wainer read-off, §3).
- **New capstone `goodstein_independent`**: `(𝗣𝗔 ⊬ ↑goodsteinSentence) ∧ (𝗣𝗔 ⊬ ∼↑goodsteinSentence)` —
  the ¬-half is cheap: Foundation soundness + `Bridge` + `goodstein_terminates_engine`. *This is the
  "completely" in the operator's ask — independence, not just unprovability.*
- CI: `lean-axiom-gate --exact` (3 canonical + the native base pending W7) + blueprint audit.

**W7 — `native_decide` burndown. Est 1–3 laps · 60% (fallback is acceptable).**
The 12 base facts are small arithmetic anchors, but `goodsteinSeq`/`goodsteinLength` won't
kernel-reduce (wf-recursion; `G` is `sInf`-based). Route: a fuel-twin evaluator + a proven equivalence
lemma, then `decide`/`simp` the 12 on the twin. If genuinely stuck: keep the documented native base —
the operator blessed it — but the endgame then prints 3+12 and says so plainly.

## 6. Governance

- **Statements are architect-owned; proofs are treadmill-owned.** Every reified capstone statement and
  every phase's master-theorem signature is written/audited host-side (this plan's LOCK extension);
  grind laps prove named `sorry`s inside a phase, never invent statements on the trust surface.
- **Judge verification each review lap**: real `#print axioms` on the stage chain + `blueprint_audit`;
  the calibration rule from the lap-171 review stands — *trust the ledger, not per-node confidence*.
- **ROUTE GUARD registers T-W3 and T-W4** (above) as this campaign's pre-registered triggers. A fired
  trigger forces ESCALATE, never a silent grind-through — that discipline is why Route A's death was
  caught at all.
- Route A / internal-Z stays frozen absent explicit operator reopen (unchanged).

## 7. What each phase's exit looks like (DROP-shaped, auditable)

| Phase | Exit artifact (a whole named debt DROPS) |
|---|---|
| W0 | reified ledger compiles; audit green; build-time pruned |
| W1 | `boundedAxiomLeaves` theorem, hypothesis-free |
| W2 | `boundedInduction` theorem, probe premises discharged |
| W3 | `budgetedEmbedding` master theorem |
| W4 | `operatorCutElim` master theorem |
| W5 | `fragmentProjection` theorem |
| W6 | headline + `wainer_bound…` + `goodstein_independent`, allowlist = 3 (+native) |
| W7 | allowlist = **exactly 3** |

## 8. Honest odds + the abandon branch

- Two coupled hard bets remain (W2's bounded-EM-for-arbitrary-ψ; W4's control-raising recursion), each
  ~65–70% on this architecture given the leaf-level machine validation already banked; everything else
  is conditional-high. Correlated, not independent ⇒ **engine ~55–65%**; with the `Zᵉ` fallback
  **~70–75%** overall within 3–4 months.
- Both triggers firing *and* the fallback failing = the mandate's **abandon** branch: state it plainly,
  bank the library (the `Z∞` cut-elim + operator calculus + lower bound are independently publishable
  Lean-firsts regardless), close the expedition. No third option exists under the 2026-07-01 decision,
  and this plan doesn't pretend one does.

## 9. Endgame checklist

```text
#print axioms GoodsteinPA.peano_not_proves_goodstein   -- [propext, Classical.choice, Quot.sound]
#print axioms GoodsteinPA.goodstein_independent        -- [propext, Classical.choice, Quot.sound]
lean-axiom-gate . -t GoodsteinPA.peano_not_proves_goodstein --exact   -- ✓
lake exe blueprint_audit                                -- all nodes clean, 0 capstone axioms
```

First formalized concrete PA-independence in any prover; the general Wainer classification
(`ProvablyTotal f → ∃ α < ε₀, dominated`) as the natural post-headline generalization of the same
engine — the mathlib-shaped gift `EXPEDITION-PLAN.md` predicted ("the thing mathlib lacks and every
PA-independence result needs").
