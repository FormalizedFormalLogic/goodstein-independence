# STATUS — GoodsteinPA 📊

**Kirby–Paris: `𝗣𝗔 ⊬ Goodstein`, via Towsner's Route B (Z_∞ ω-rule calculus + ε₀ cut-elimination).**
· **Build**: 🟢 green (1248 jobs) · **Updated**: lap 5 · 2026-06-22

## ⚡ LAP-5 BREAKTHROUGH — the gAll/I∀ lower-bound frontier is RESOLVED (machine-checked)
The lap-4 "accumulating existentials" wall (the hardest piece, Towsner Thm 17.1 `I∀` case) is down.
- **Hardy hierarchy ported** to `src/GoodsteinPA/Hardy.lean` (from Track-1; mathlib revs identical):
  `hardy`/`norm` = Towsner `h_α`/`τ`, `hardy_le_of_lt` = **Hmono**, `hardy_monotone` = **Hmono_n**.
- **`lowerBound_existential_hardy`** (`wip/LowerBoundHardy.lean`): ∀-free lower bound, **zero abstract
  hypotheses**, over the real Hardy hierarchy + real `G`. Calculus `B` re-stated over `ONote` (= `<ε₀`).
- **`B.allInv`** (∀-inversion) + **`lowerBound_hardy`** = the **full Thm 17.1 modulo domination `Hdom`**.
  Resolution: invert `gAll` away (don't carry it through the induction — a set-sequent `gAll` lets the
  ω-rule re-expand at a small reachable index and `trueR`-close everything, breaking a direct
  invariant). All axiom-clean. See `ANALYSIS-2026-06-22-bounding-resolution.md`.
- **Next:** discharge `Hdom : ∃ x, hardy α (max k x) < G x` — `G = goodsteinLength`, Goodstein defs
  byte-identical to Track-1, so PORT `goodsteinLength_dominates_fastGrowing` (+ `hardy ≤ fastGrowing`,
  bridge the `+2` to strict). Then M4 embedding + M7 assembly remain for the headline.

## Where it stands
Phase 0 (encoding + faithfulness bridge) and Phase 1 (Gödel II hook) are landed and axiom-clean.
The **deep core of Phase 2 — Gentzen-style cut-elimination for the infinitary `Z_∞` calculus
(milestone M5, Towsner §19) — is COMPLETE and `#print axioms`-clean** in `src/GoodsteinPA/Zinfty.lean`.
The headline `Statement.peano_not_proves_goodstein` is still a literal `sorry` (anti-fraud).

## ⚠️ LAP-4 ARCHITECTURAL FINDING — the witness bound is essential (course correction)
The completed M5 cut-elimination is for a calculus whose `∃`-rule (`Deriv.exI`) puts **no bound on
the witness numeral**, and whose ordinal measure `o` does **not** track Towsner's numeric index `k`.
That calculus **cannot reach the headline**: its cut-free fragment *proves* the Goodstein sentence
`∀x∃y g_y(x)=0` at ordinal **2** (witness = `G(n)` directly), so Towsner's lower bound (Thm 17.1) is
**false** for it. The three-theorem sandwich (16.7 embed ⟹ 19.9 cut-elim ⟹ 17.1 lower bound) only
closes if **all three** track the witness/Hardy bound `value(t) ≤ h_α(k)`. M5 dropped it (correct
*for cut-elimination in isolation* — the prior lap's "k not needed" claim — but a dead end for the
chain). **Machine-checked both directions this lap** in `wip/WitnessBound.lean`, axiom-clean:
- `unbounded_proves_goodstein` : the witness-**unbounded** cut-free calculus derives `gAll` at `2`.
- `lowerBound_existential` : the witness-**bounded** calculus *cannot* derive the `∀`-free existential
  fragment once `h α k < G n` — the irreducible reason the bound bites.

**Consequence for the roadmap:** the load-bearing girder is now the **witness-bounded, Hardy-indexed
`(α,k)` calculus** `B` + the full lower bound (Thm 17.1). The `src/Zinfty.lean` cut-elimination stays
as a verified *component* but is **off the headline path** until cut-elimination is redone tracking
`k` (its inversion/reduction *strategy* ports; only the bound bookkeeping changes). The further gap:
our headline is real-`ℒₒᵣ` PA with an **opaque Σ₁** `goodsteinSentence`, not Towsner's extended-language
`∀x∃y g_y(x)=0`, so a PA↔PA⁺ arithmetization bridge is *also* needed (Towsner Remark 10.3 skips it).

## What's happened (newest first)
- **2026-06-22 (lap 4):** Ground-truthed Towsner §10–§19 against the Lean. Found + machine-checked
  (axiom-clean, `wip/WitnessBound.lean`) the **witness-bound gap** above: built the witness-bounded
  Hardy-indexed calculus `B`, proved the existential-fragment lower bound, and proved the unbounded
  calculus collapses. Identified an invariant subtlety in Towsner's *full* 17.1 (accumulating
  existentials under the `I∀` ω-rule) — filed `ON-LINE-REQUEST.md` for the rigorous invariant.
- **2026-06-22 (lap 3):** Proved the ENTIRE Z_∞ cut-elimination (Towsner §19), zero sorries,
  axiom-clean: inversions (done prior) + cut reductions §19.5 (∧/∨, via double-inversion) & §19.6
  (∀/∃, by induction on the ∃-side) + `cutElimStep` §19.7 (rank `c+1→c`, all 8 cases + 8-way cut
  dispatch) + `cutElim` §19.9. Atomic (`rel`/`nrel`) cuts via `atomCut` and `⊥` cuts via
  `removeFalsum` — both needing NO truth layer (set-sequent idempotence dissolves them). Found
  `Ordinal.nadd` ABSENT from mathlib v4.31.0 → used ordinary `+` with `+1` slack, bounded by
  additive principality of `ω^c`. Restricted `exI` to numeral witnesses (for §19.6 matching).
  Promoted `wip/ZinftyF.lean → src/GoodsteinPA/Zinfty.lean`. (M5 ✅)
- **2026-06-22 (lap 2):** Built the real `Z_∞` calculus over Foundation's `SyntacticFormula ℒₒᵣ`
  with set sequents; proved all three inversion lemmas (§19.2–19.4); reduced cut-elimination to
  the lone `cutElimStep` leaf.
- **2026-06-22 (lap 1):** M1 (`goodsteinTerminates_re`, Phase 0 axiom-clean), M2 (`Reduction.lean`
  Gödel II hook), Phase-2 decomposition doc (Towsner-grounded ladder).

## Outstanding
### Short-term (mirror PENDING_WORK top)
- **M4 — embedding `PA⁺ ↪ Z_∞`** (Towsner §16, Thm 16.7 / §18 Thm 18.1): every PA proof of `φ`
  yields `Z_∞ ⊢^{α,k}_c φ` with `α < ε₀`, finite `c`. The next major girder. Reuse Foundation's
  finitary `Derivation`; map each rule across, finitary `∀` → ω-rule. Needs: induction-axiom
  derivability (Lemma 16.5/Cor 16.6) at bound `ω·4 # 2rk(φ) # 8`.
- **M6 — cut-free lower bound** (Towsner §17, Thm 17.1): no cut-free `Z_∞ ⊢^α_0 ∀x∃y g_y(x)=0`
  for any `α < ε₀`, because Goodstein length dominates every Hardy `h_α`. Largely parallel to M4;
  M6.1–M6.3 (Hardy hierarchy) overlap Track 1 (`~/src/lean-formalizations` `Logic/FastGrowing`).
### Long-term
- M7 assembly (Towsner Thm 20.1): connect `∀x∃y g_y(x)=0` to our `goodsteinSentence`, chain
  M4 ⟹ M5 ⟹ M6 ⟹ contradiction, discharge the headline `sorry`.
- The `k`/Hardy numeric index: NOT in the current `(α,c)` `Provable`. Cut-elimination didn't need
  it; M6 (lower bound) likely does (Towsner threads `h_{ω^α}(k)`). Re-assess when M6 starts.
### To completion
Headline discharged ⟺ M4 + M6 + M7 land AND `#print axioms peano_not_proves_goodstein` is clean
(Route B should be `[propext, Classical.choice, Quot.sound]`, no `PA_delta1Definable`).

## Axiom ledger (per headline / landmark theorem — the fidelity spine)
| theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `peano_not_proves_goodstein` (headline) | uncond. (Kirby–Paris) | `propext, sorryAx, choice, Quot.sound` | 🔓 open `sorry` — M4+M6+M7 remain; **0** real math axioms yet |
| `goodsteinSentence_faithful` (bridge) | encoding correctness | `propext, choice, Quot.sound` | 🟢 clean (trust base only) |
| `goodsteinTerminates_re` (M1) | r.e. of termination | `propext, choice, Quot.sound` | 🟢 clean |
| `Deriv.Provable.cutElim` (M5, §19.9) | ε₀ cut-elimination | `propext, choice, Quot.sound` | 🟢 clean — **NEW this lap** |
| `Deriv.Provable.cutElimStep` (§19.7) | rank reduction | `propext, choice, Quot.sound` | 🟢 clean |
| `Deriv.Provable.atomCut` (§19.2 content) | atomic cut elim | `propext, choice, Quot.sound` | 🟢 clean |
| `not_proves_of_implies_consistency` (Route A) | meta-reduction | `…, PA_delta1Definable` | 🟡 Foundation axiom; **Route A only** — Route B avoids it |
| `unbounded_proves_goodstein` (lap-4, `wip/`) | gap demo: no lower bound w/o witness bound | `propext, choice, Quot.sound` | 🟢 clean — proves current `Zinfty` calc is a dead end |
| `lowerBound_existential` (lap-4, `wip/`) | ∃-fragment of Thm 17.1 (witness-bounded) | `propext, choice, Quot.sound` | 🟢 clean — the witness-bound mechanism, proven |
| `hardy_le_of_lt` (lap-5, `src/Hardy`) | Hardy index monotonicity (Hmono) | `propext, choice, Quot.sound` | 🟢 clean — ported Track-1 |
| `lowerBound_existential_hardy` (lap-5, `wip/`) | ∃-fragment 17.1, concrete Hardy/`G` | `propext, choice, Quot.sound` | 🟢 clean — **zero abstract hyps** |
| `B.allInv` (lap-5, `wip/`) | ∀-inversion (the I∀-frontier resolution) | `propext, choice, Quot.sound` | 🟢 clean |
| `lowerBound_hardy` (lap-5, `wip/`) | **full Thm 17.1** mod `Hdom` | `propext, choice, Quot.sound` | 🟢 clean — gAll case RESOLVED, modulo domination |

Math-axiom count on the (eventual) Route-B headline target: **0** beyond the trust base — every
proven component is `[propext, Classical.choice, Quot.sound]`. The `sorryAx` on the headline is the
honest open marker, not a smuggled axiom. (`PA_delta1Definable` is 🟡 but sits only under the
unused Route-A hook, never on the Route-B chain.)

## Pointers
ROADMAP/plan: `EXPEDITION-PLAN.md`, `PHASE2-DECOMPOSITION.md` · newest baton: `HANDOFF-2026-06-22.md`
· open-items: `PENDING_WORK.md` · charter: `DIRECTION.md`
