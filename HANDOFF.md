# HANDOFF — 2026-06-22 (lap 14)

> **Branch** `plan` · build **green** (`lake build GoodsteinPA`, 1264 jobs) · headline
> `peano_not_proves_goodstein` = honest `sorry` (anti-fraud guard intact, untouched).
> **Lap 14 CRACKED THE CRUX: Boundedness Thm 5.4 (Buchholz §5) is COMPLETE and axiom-clean**
> — the one open theorem that gated the whole Buchholz route. Plus its order-type corollary.

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
| **A** Boundedness Thm 5.4 | the crux | ✅ **DONE this lap, axiom-clean** |
| **B** Corollary `‖≺‖≤2^β` | TI/∀-inversion glue → feed `orderType_le_of_deriv` | core ✅; needs the inversion wrapper + cut-elim to `c=0`, all **XFreeAx-preserving** |
| **C** M4 `embedC` over `LX` | mechanical `{L}`-generalize (like M5/`ZinftyGen`); **route X-atom identity axioms through `axL`, not `axTrue`**, so embedded derivations are `XFreeAx` | not started, ~1–2 laps |
| **D** Thm 5.6 | 5.5 + `cutElim`→c=0 + B | ~1 lap |
| **E** Goodstein⟹TI_≺(X) bridge | Kirby–Paris; reuse Phase-0 CNF-ε₀ encoding | ~2 laps |
| **F ★** Arithmetization seam | ℒₒᵣ-definable ε₀ order, `‖≺‖=ε₀`, **discharge `hprec`/`hprecXPos`** | ~2–3 laps — the 2nd hard wall |
| **G** Final assembly | chain + `#print axioms` clean | ~1 lap |

**NEXT (lap 15): start C (`embedC` over LX).** Reuse the `ZinftyGen` `{L}`-generic pattern. KEY
faithfulness requirement: the embedding must produce **`XFreeAx` derivations** — so X-atom logical
axioms (`Xs ∨ ¬Xs` / substitution-of-equals) must be derived via **`Deriv.axL`** (the complementary
pair, no truth needed), NEVER `Deriv.axTrue` on an X-relation. PA(X) axioms are X-free (true under
`structLX S` for any S, induction included), so their leaves are X-free `axTrue`/`axL` automatically.
Also need: a `cutElim`-to-`c=0` + TI/∀ inversion wrapper that **preserves `XFreeAx`** (same `PXF`
trick as `andInv_xfree`; `cutElim`'s reductions must not introduce X-`axTrue` leaves — verify).

## Notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `sorry`.
- **Build:** `lake build GoodsteinPA` (1264). The `ambient` instance is `structLX ∅` (X=∅) so a lone
  positive X-`axTrue` is impossible and `XFreeAx` only needs to forbid `axTrue false Xsym _` leaves.
- **Literature on disk:** Buchholz §5 = the route (`papers/buchholz-…lecture-notes.pdf` pp.27–31;
  case structure quoted in `ANALYSIS-2026-06-22-lap13-boundedness-design.md`). `WebSearch` ok, `WebFetch` dead.
- **Aristotle:** idle. Good targets for C: an `XFreeAx`-preserving cut-elim/inversion lemma, or an
  `embedC.axm` PA(X)-axiom case once its statement is pinned. No open `ON-LINE-REQUEST.md`.
- **Banked off-path (do NOT resume):** witness-bounded `wip/` calculi (Towsner/operator-H); `Zᵏ`/M6.

## Lap-14 commits (12)
models connective layer · rk_le_of_forall · Boundedness defs (ambient/tval/XFreeAx/Partition/SatPos) ·
base cases (axL incl X-pair/axTrue/verumR/weak/cut) · xpos_rew + satpos helpers · andI/orI · allω +
exI(X-positive) · case-2 helpers + hprec couplings · **case 2 (¬Prog inversion)** · **Boundedness
COMPLETE via andInv_xfree (PXF)** · **orderType_le_of_deriv corollary**.
