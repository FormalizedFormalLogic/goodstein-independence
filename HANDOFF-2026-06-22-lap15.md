# HANDOFF — 2026-06-22 (lap 15)

> **Branch** `plan` · build **green** (`lake build GoodsteinPA`, 1265 jobs) · headline
> `peano_not_proves_goodstein` = honest `sorry` (anti-fraud guard intact, untouched).
> **Lap 15 (review + grind) CLOSED C₁ + D + the C₂ CRUX, all axiom-clean.** `XFreeCutElim.lean` (1456
> lines): the `XFreeAx`-preserving cut-elimination (C₁), the Thm-5.6 tail `PXFc α c {TI} ⟹ ‖≺‖ ≤ 2^(ω_c^α)`
> (D), the `LX` excluded-middle `provable_em_x`, and **`metaInduction`** — the faithfulness-critical
> X-induction embedding (the part lap-14 flagged CRITICAL). **Remaining to Thm 5.6: the C₂ *structural*
> `embedC` port (mechanical, but its target schema is entangled with F).** Then E + F.

## Lap-15 review finding (validated the lap-14 design — see STATUS "What's happened")
The lap-14 cr=0 design was feared obstructed (X-atomic cuts seemingly un-eliminable while preserving
`XFreeAx`). **Resolved by reading `atomCutAux`:** our `Provable.axL` is the *same-atom* EM axiom
`{Xs,¬Xs}`, so X-atomic cuts close by **set idempotence** (no truth), and the truth-surgery branch
(`removeFalseLit`) is **vacuous under `XFreeAx`** (it needs an X-`axTrue` leaf). So C₁ is feasible as
written — confirmed by completing it.

## ✅ Lap-15 deliverable: C₁ + D (`src/GoodsteinPA/XFreeCutElim.lean`, axiom-clean)
The whole §19 cut-elimination, ported to a cut-rank-carrying `XFreeAx`-tracking twin
`PXFc α c Γ := ∃ d : Deriv Γ, d.o ≤ α ∧ d.cr ≤ c ∧ XFreeAx d` (generalises lap-14 `PXF = PXFc · 0`):
- **Builders** `PXFc.{mono,weakening,cast,axL,axTrue,verumR,andI,orI,exI,allω,cut,contr}` + bridges
  `PXF.toPXFc`/`PXFc.toPXF`.
- **Inversions at cut rank ≤ c** (real `cut` case now, not the lap-14 vacuous one): `orInvAux_x`,
  `andInvAux_x` (+`PXFc.andInvL/R`), `allInvAux_x` (+`PXFc.{orInv,allInv}`).
- **Cut reductions** `PXFc.{cutReduceConj,cutReduceDisj,cutReduceAllAux,cutReduceAll}` (§19.5/19.6).
- **Truth layer** `PXFc.{removeFalseLitAux,removeFalsumAux,removeFalsum,atomCutAux,atomCut}`. Key:
  `removeFalseLitAux` carries `Sum.isLeft r₀ = true` (X-free removed atom ⟹ X-free `axTrue` leaves);
  `atomCutAux`'s truth branch extracts that via **`xfree_transport`** (an `axTrue` leaf equal to the cut
  atom is X-free, so the cut atom is X-free; at an X-atom cut the branch is vacuous).
- **Assembly** `PXFc.{cutElimPrincipal,cutElimStepAux,cutElimStep,cutElim}` (§19.7/19.9):
  `cutElim : PXFc α c Γ → PXFc (omegaTower c α) 0 Γ`. **C₁.**
- **D** `orderType_le_of_TIprovable` = `PXFc.cutElim ∘ orderType_le_of_TIderiv` (corollary B):
  `PXFc α c {TI prec} ⟹ ‖≺‖ ≤ 2^(ω_c^α)` (given the legit seam hyps `hprec`/`hprecXPos`). **Thm 5.6 tail.**
- **C₂ groundwork** `provable_em_x` — `Z∞` excluded middle over `LX` → `PXFc · 0` (atoms close via
  same-atom `axL`, **never `axTrue`**, so `XFreeAx` is automatic; works for X-atoms too).
- **C₂ CRUX** `metaInduction` — the X-induction embedding via a **tower of `cut`s on `ψ(i)` +
  `provable_em_x`** (Buchholz Thm 5.5 induction case), `XFreeAx`-preserving. Stated abstractly in the
  families `ψ/[nm n]` with the inverted step `(∼step)/[nm n] = ψ(n) ⋏ ∼ψ(n+1)` as a hypothesis. **This
  is the faithfulness-critical case the lap-14 HANDOFF flagged CRITICAL — now machine-checked.** The
  Foundation-DSL that builds `step` from `ψ` by the successor substitution is the only `axm`-X-case glue left.

## 🎯 Critical path to the headline (★ = real walls)
| Step | What | Status |
|---|---|---|
| **A** Boundedness Thm 5.4 | crux | ✅ DONE lap 14, axiom-clean |
| **B** Corollary `‖≺‖≤2^β` | invert TI + Boundedness | ✅ DONE lap 14, axiom-clean |
| **C₁** `XFreeAx` cutElim → cr=0 | the big §19 port | ✅ **DONE lap 15, axiom-clean** |
| **D** Thm 5.6 tail | C₁ ∘ B | ✅ **DONE lap 15** (`orderType_le_of_TIprovable`) |
| **C₂-crux** X-induction meta-induction + LX-EM | the faithfulness-critical case | ✅ **DONE lap 15** (`metaInduction`, `provable_em_x`) |
| **C₂-struct** `embedC` structural port over `LX` | mechanical (mirror `src/Embedding`); target schema entangled w/ F | **NEXT** |
| **E** Goodstein⟹TI_≺(X) bridge | Kirby–Paris; reuse Phase-0 CNF-ε₀ | not started |
| **F ★** Arithmetization seam | ℒₒᵣ-def ε₀ order, `‖≺‖=ε₀`, discharge `hprec`/`hprecXPos` | not started — 2nd hard wall |
| **G** Final assembly | chain + `#print axioms` clean | not started |

## NEXT (lap 16): C₂ — the `embedC` STRUCTURAL port over `LX` (the crux `metaInduction` is DONE)
What remains of C₂ is the **structural** embedding: induct on `Derivation2 (𝗣𝗔(LX):Schema) Γ`, emit a
`PXFc`. The genuine-doubt pieces are already machine-checked — `metaInduction` (X-induction) and
`provable_em_x` (EM). The rest mirrors `src/Embedding.lean`'s `embedC` (lines 525–660), swapping
`ZinftyF`/`ℒₒᵣ` → `ZinftyGen`/`LX` and `Provable` → `PXFc`:
- **structural cases** (`closed,verum,and,or,all,wk,shift,cut`) — mechanical (the `asg e`-assignment
  reformulation + `Finset.image` plumbing ports verbatim; all use `XFreeAx`-safe builders).
- **`axm`** — split: **`𝗣𝗔⁻(LX)` X-free axioms** via a `provable_true_x` (ω-completeness; needs porting
  `provable_true`, X-free `axTrue` ⟹ `XFreeAx`-safe); **X-induction `Ind_φ`** via **`metaInduction`** —
  the remaining glue is the Foundation-DSL building `step` from `ψ` (the successor substitution) +
  proving `metaInduction`'s `hstep` (`(∼step)/[nm n] = ψ(n) ⋏ ∼ψ(n+1)`) + stripping `univCl`/the two `🡒`
  to reach `metaInduction`'s sequent shape.
- **`exs`** — port `exI_closed`/`provable_em_cong_gen` (value-congruent EM); `axTrue`s on `ψ/[s]`, safe
  iff `ψ` X-free — verify the TI embedding never value-congruences an X-atom (likely fine).

⚠️ **Entanglement with F:** the *target schema* (`𝗣𝗔(LX)` = `PeanoMinus LX` + `InductionScheme LX`,
and how the hypothetical `Z ⊢ TI(X)` is even stated) depends on the arithmetization seam F (the ε₀-order
`prec`, not yet built). Resolve "what is `Z ⊢ TI(X)` in Lean?" early in lap 16 — check whether Foundation
gives `PeanoMinus`/`InductionScheme` generically over an `ORing` language (it likely does), and decide
whether to port `embedC` generically over `{L}` (reusable for ℒₒᵣ too) or LX-specifically.
Deliverable: `embedC_LX : (𝗣𝗔(LX) ⊢ TI(X)) → ∃ c α, PXFc α c {TI prec}`. Then **D (`orderType_le_of_
TIprovable`) fires** ⟹ Thm 5.6 ⟹ `PA ⊬ TI(ε₀)` modulo F.

## Notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `sorry`.
- **Aristotle:** idle (jobs all IDLE). Good C₂ target: a self-contained `provable_em`-over-LX X-atom
  case, or the meta-induction `cut`-tower lemma (inline defs). No open `ON-LINE-REQUEST.md`.
- **Banked off-path (do NOT resume):** witness-bounded `wip/` calculi; `Zᵏ`/M6.
- Build: `lake build GoodsteinPA` (1265). See `STATUS.md` for the full overview + axiom ledger.
