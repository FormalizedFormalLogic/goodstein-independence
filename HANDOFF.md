# HANDOFF — 2026-06-22 (lap 14)

> **Branch** `plan` · build **green** (`lake build GoodsteinPA`, 1264 jobs) · headline
> `peano_not_proves_goodstein` = honest `sorry` (anti-fraud guard intact, untouched).
> **Lap 14 CRACKED THE CRUX *and* CLOSED THE COROLLARY: Boundedness Thm 5.4 + the full
> `Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β` corollary are COMPLETE and axiom-clean** (modulo the two
> legitimate `hprec`/`hprecXPos` inputs, discharged at the arithmetization seam). Steps A + B done.
> All 17 lap-14 deliverables are `[propext,choice,Quot.sound]` — no `sorryAx`, no math axioms.

## ✅ Lap-14 headline: steps A + B of the Buchholz route, axiom-clean
- **A. `boundedness` (Thm 5.4)** — the crux. 9-case nested induction (outer on height, inner
  structural); hardest case 2 (`¬Prog` inversion + `α→α+2^{β₀}` rank bump) machine-checked.
- **B. `orderType_le_of_TIderiv`** — the FULL corollary: from one cut-free `XFreeAx` derivation of
  `{TI_≺(X)}` (height `≤ β`), invert (`orInv_xfree` on `🡒`, `allInv_xfree` on `∀x`) to
  `{¬Prog, X(nm n)}` ∀n, apply Boundedness ⟹ `‖≺‖ ≤ 2^β`. **This is Buchholz's corollary, done.**
- Built the **`PXF`** framework (cut-free `XFreeAx`-tracking provability + smart constructors) and the
  full **`XFreeAx`-preserving inversion suite**: `andInv_xfree`, `orInv_xfree`, `allInv_xfree`.

### The ONE remaining input to B (⟹ the whole order-type bound): a cut-free `XFreeAx` `⊢{TI}`
`orderType_le_of_TIderiv` consumes `d : Deriv {TI prec}` with `d.cr = 0 ∧ XFreeAx d ∧ d.o ≤ β`.
That derivation = **`embedC`(`Z ⊢ TI`) [step C] + `cutElim`→c=0 [must preserve `XFreeAx`]**. Once those
two land, B fires and `‖≺‖ ≤ 2^β` is unconditional (given the order satisfies `hprec`/`hprecXPos`).

## ✅ Lap-14 deliverables (all in `src/GoodsteinPA/Boundedness.lean`, axiom-clean `[propext,choice,Quot.sound]`)

1. **`boundedness` (Thm 5.4)** — THE crux. For an X-positive-decomposed sequent (every member is
   `¬Prog_≺(X)`, a bounded `¬Xt`, or X-positive), a **cut-free `XFreeAx`** derivation of height `o d`
   yields `⊨^{α+2^{o d}}` of some X-positive member. **All 9 `Deriv` constructor cases proven**,
   including the hard **case 2** (`∃⁰χ = ¬Prog`): extract `χ = ∼(hyp 🡒 X#0)`, `χ/[nm n] = φ₁ ⋏ φ₂`,
   invert (`andInv_xfree`), feed the two outer-IH calls, and do the **`α → α+2^{β₀}` rank bump**
   (`models φ₁ ⟹ |n|_≺ ≤ α+2^{β₀}`, then `(α+2^{β₀})+2^{β₀} = α+2^{β₀+1} ≤ α+2^β`). Proof is a
   **nested induction**: outer strong induction on the ordinal height `o d` (case 2's inversions
   shrink it strictly), inner structural induction on `d` (the height-preserving cases).
2. **`andInv_xfree`** — the `XFreeAx`-preserving ∧-inversion (Buchholz needs the inverted derivations
   to keep the no-lone-X-leaf condition). Replays `ZinftyGen.andInvAux` at cut-rank 0 (so the `cut`
   case is vacuous) via the new **`PXF`** carrier (`∃ d, o≤α ∧ cr=0 ∧ XFreeAx d`) + its smart
   constructors (`PXF.axL/axTrue/verumR/weak/andI/orI/allω/exI`). Was the last gap; now closed.
3. **`orderType_le_of_deriv` (Corollary core)** — from a cut-free `XFreeAx` derivation of
   `{¬Prog_≺(X), X(nm n)}` (height `≤ β`) for **every** `n`, concludes `‖≺‖ ≤ 2^β`. Wires Boundedness
   straight into the order-type bound. **This is the `Z∞ ⊢^β_1 TI ⟹ ‖≺‖ ≤ 2^β` corollary minus the
   TI/∀ inversion glue** (`embedC`+`cutElim` supply the derivation).
4. Supporting (reusable): `TruthSem.models_and/or/all/ex` (`⊨^γ` connective layer), `rk_le_of_forall`
   (`∀m≺n, |m|<γ ⟹ |n|≤γ`), `xpos_rew`/`xpos_subst` (X-positivity is substitution-invariant),
   `satpos_mono`/`satpos_subset`, `models_Xat'`/`models_negXat`/`models_inl_lit`, `chi_subst`/
   `xat_subst`/`hyp_xpos`/`tval_nm`.

### Two legitimate hypotheses on `boundedness`/`orderType_le_of_deriv` (NOT axioms — discharged later)
- **`hprec`** `∀ γ n, ⊨^γ((hyp prec)/[nm n]) ↔ ∀ m≺n, |m|_≺<γ` — the semantic spec of the order
  formula `prec` (its ℕ-interpretation = the wellfounded `lt`).
- **`hprecXPos`** `XPos (∼prec)` — the order literal is X-free.
Both hold for the headline's ℒₒᵣ-definable ε₀ order; **discharged at the arithmetization seam (F)**.

## 🎯 Critical path to the headline (≈ 8 laps; ★ = the two real walls left)

| Step | What | Status |
|---|---|---|
| **A** Boundedness Thm 5.4 | the crux | ✅ **DONE, axiom-clean** |
| **B** Corollary `‖≺‖≤2^β` | invert `{TI}`→`{¬Prog,Xn}` + Boundedness | ✅ **DONE, axiom-clean** (`orderType_le_of_TIderiv`); needs a cut-free `XFreeAx` `⊢{TI}` as input |
| **C₁** `cutElim` → `c=0`, **`XFreeAx`-preserving** | port `ZinftyGen` cut-elim to a cut-rank-carrying `PXFc` twin (`∃d, o≤α ∧ cr≤c ∧ XFreeAx d`); reductions = inversions (done) + structural builders, no new X-`axTrue` | not started, ~1–2 laps (the big port) |
| **C₂** M4 `embedC` over `LX` | mechanical `{L}`-generalize (like M5/`ZinftyGen`); **route X-atom identity via `Deriv.axL`, never `axTrue`**, ⟹ `XFreeAx` | not started, ~1–2 laps |
| **D** Thm 5.6 | `embedC`(C₂) + `cutElim`(C₁) → `XFreeAx ⊢{TI}` → B | ~0.5 lap once C₁,C₂ land |
| **E** Goodstein⟹TI_≺(X) bridge | Kirby–Paris; reuse Phase-0 CNF-ε₀ encoding | ~2 laps |
| **F ★** Arithmetization seam | ℒₒᵣ-definable ε₀ order, `‖≺‖=ε₀`, **discharge `hprec`/`hprecXPos`** | ~2–3 laps — the 2nd hard wall |
| **G** Final assembly | chain + `#print axioms` clean | ~1 lap |

**NEXT (lap 15): C₁ (cut-elim `XFreeAx`-preserving) and/or C₂ (`embedC` over LX).** Both are
mechanical PXF-style ports; C₁ reuses the inversion suite already built this lap. For C₁: introduce
`PXFc α c Γ := ∃ d, d.o≤α ∧ d.cr≤c ∧ XFreeAx d` and port `cutReduceConj/Disj/AllAux` + `cutElimStep` +
`cutElim` (the reductions only compose inversions [done] + builders + `cut`, none add X-`axTrue`). For
C₂ — **CRITICAL faithfulness correction (lap-14 finding, supersedes earlier note):** the existing
`embedC.axm` derives PA axioms via **`provable_true`** (ω-completeness, `axTrue` at atomic leaves).
Over ℒₒᵣ that's fine, but over `LX` **the induction scheme `Ind_φ` for an X-*formula* `φ` contains
X-atoms**, so `provable_true Ind_φ` would `axTrue` on a lone X-atom ⟹ **breaks `XFreeAx`**. So the LX
port MUST derive the induction axioms **via the meta-induction (a tower of `cut`s on `φ(n)` + `provable_em`
base/step)** — Buchholz Thm 5.5's actual method, NOT ω-completeness. `provable_em` for X-atoms already
uses `Deriv.axL` (the X-pair, no truth) ✓, so the meta-induction route is `XFreeAx`-safe. The lap-10
HANDOFF/PENDING has the full meta-induction proof worked out — port THAT for the X-induction case.
`𝗣𝗔⁻` axioms (PeanoMinus, finite, X-free) can still go via `provable_true` (X-free `axTrue` ✓).
`provable_em_cong_gen` (`exs`/`exI_closed`) `axTrue`s on `ψ/[s]`: safe iff `ψ` is X-free — check the TI
embedding never value-congruences an X-atom (likely fine: `prec` X-free, witnesses are ℒₒᵣ terms).

## Notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `sorry`.
- **Build:** `lake build GoodsteinPA` (1264). The `ambient` instance is `structLX ∅` (X=∅) so a lone
  positive X-`axTrue` is impossible and `XFreeAx` only needs to forbid `axTrue false Xsym _` leaves.
- **Literature on disk:** Buchholz §5 = the route (`papers/buchholz-…lecture-notes.pdf` pp.27–31;
  case structure quoted in `ANALYSIS-2026-06-22-lap13-boundedness-design.md`). `WebSearch` ok, `WebFetch` dead.
- **Aristotle:** idle. Good targets for C: an `XFreeAx`-preserving cut-elim/inversion lemma, or an
  `embedC.axm` PA(X)-axiom case once its statement is pinned. No open `ON-LINE-REQUEST.md`.
- **Banked off-path (do NOT resume):** witness-bounded `wip/` calculi (Towsner/operator-H); `Zᵏ`/M6.

## Lap-14 commits (~16)
models connective layer · rk_le_of_forall · Boundedness defs · base cases · xpos_rew + satpos helpers ·
andI/orI · allω + exI(X-positive) · case-2 helpers + hprec couplings · **case 2 (¬Prog inversion)** ·
**Boundedness COMPLETE via andInv_xfree (PXF)** · **orderType_le_of_deriv** · orInv_xfree · allInv_xfree ·
**orderType_le_of_TIderiv (full corollary B)** · HANDOFF.
