# STATUS — GoodsteinPA 📊

**Kirby–Paris: `𝗣𝗔 ⊬ Goodstein`, via Towsner's Route B (Z_∞ ω-rule calculus + ε₀ cut-elimination).**
· **Build**: 🟢 green (1243 jobs) · **Updated**: lap 3 · 2026-06-22 · `4f08ed3`+promotion

## Where it stands
Phase 0 (encoding + faithfulness bridge) and Phase 1 (Gödel II hook) are landed and axiom-clean.
The **deep core of Phase 2 — Gentzen-style cut-elimination for the infinitary `Z_∞` calculus
(milestone M5, Towsner §19) — is now COMPLETE and `#print axioms`-clean**, living in
`src/GoodsteinPA/Zinfty.lean` (promoted from `wip/` this lap). The headline
`Statement.peano_not_proves_goodstein` is still a literal `sorry` (anti-fraud): it needs the
remaining girders M4 (embedding `PA⁺ ↪ Z_∞`), M6 (cut-free lower bound), and M7 (assembly), none
of which is started. A surprising win this lap: **no truth/soundness layer was needed** for the
atomic/`⊥` cut cases — set sequents dissolve them.

## What's happened (newest first)
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

Math-axiom count on the (eventual) Route-B headline target: **0** beyond the trust base — every
proven component is `[propext, Classical.choice, Quot.sound]`. The `sorryAx` on the headline is the
honest open marker, not a smuggled axiom. (`PA_delta1Definable` is 🟡 but sits only under the
unused Route-A hook, never on the Route-B chain.)

## Pointers
ROADMAP/plan: `EXPEDITION-PLAN.md`, `PHASE2-DECOMPOSITION.md` · newest baton: `HANDOFF-2026-06-22.md`
· open-items: `PENDING_WORK.md` · charter: `DIRECTION.md`
