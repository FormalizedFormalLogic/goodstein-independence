# HANDOFF — 2026-06-22 (lap 16)

> **Branch** `plan` · build **green** (`lake build GoodsteinPA`, 1266 jobs) · headline
> `peano_not_proves_goodstein` = honest `sorry` (anti-fraud guard intact, untouched).
> **Lap 16: C₂ structural embedding `embedC_LX_gen` (9/10) + `provable_true_x` (new
> `src/GoodsteinPA/EmbeddingX.lean`), AND the value-congruent literal-axiom retrofit `Deriv.axLv`
> (Buchholz `AX(Z∞)` p.27) landed across ZinftyGen/Boundedness/XFreeCutElim.** Build green; **2 C₂
> `sorry`s left** — `exs` (EmbeddingX) and `atomCut_x` X-atom-cut (XFreeCutElim), both unblocked by the
> single lemma `nrel_value_subst` (see NEXT). C₁/D temporarily carry the `atomCut_x` sorry.

## ✅ Lap-16 deliverables (`src/GoodsteinPA/EmbeddingX.lean`, axiom-clean modulo the one disclosed sorry)
- **`XFreeForm`** — structural "every relation symbol is `ℒₒᵣ` (`Sum.isLeft`)" predicate over `LX`,
  with simp lemmas + rewriting-invariance (`xfreeForm_rew`).
- **`provable_true_x`** — ω-completeness for TRUE **closed X-free** formulas, `XFreeAx`-safe (atoms via
  `PXFc.axTrue` + the `XFreeForm` witness). The X-free `axm` engine.
- **`embedC_LX_gen`** — the `axm`-abstracted structural embedding
  `(hax) → Derivation2 𝓢 Γ → ∃ c, ∀ e, ∃ α, PXFc α c (Γ.image (asgX e ▹))`. Ports `Embedding.embedC`
  rule-by-rule to `LX`/`PXFc`: `closed` (via `provable_em_x`, `axL`-only) + all 8 structural cases
  (`verum/and/or/all/wk/shift/cut` + `axm`-as-hypothesis), every builder `XFreeAx`-safe. **`exs` is the
  one disclosed `sorry`** — the genuine wall (below).

## 🧱 THE WALL lap-15 mis-scoped — `exs` needs Buchholz's value-congruent literal axiom
Read `ANALYSIS-2026-06-22-lap16-exs-axLv.md` (full detail, grounded in the Buchholz lecture notes
§5 pp.26–30, **read this lap**). Summary:
- `embedC`'s `exs` collapses the closed witness `asgX e t` to a numeral via a **value-congruent EM**.
  For an **X-atom body** (and `∼TI`'s `∃x(hyp(x) ∧ ¬X(x))` HAS one) that collapse needs
  `⊢ X(nm m), ¬X(asgX e t)` with `|nm m|=|asgX e t|=m` — Buchholz's **value-congruent X-pair axiom**
  `{Xs,¬Xt}` (`sᴺ=tᴺ`, `AX(Z∞)`, p.27). Our `Deriv.axL` is **same-atom** `{Xs,¬Xs}` only; the pair is
  NOT `XFreeAx`-derivable (axL needs identical atoms; axTrue on X breaks `XFreeAx`).
- **Fix = generalise the literal axiom to value-congruent pairs** (new `Deriv.axLv (r) (v v') (hval) …`,
  generic over `L`, sound). Boundedness case 1.2 (p.29) and cut-elim's literal-cut case (Remark p.27)
  **already handle value-congruent pairs in Buchholz** — our same-atom versions are the special case.

## 🎯 Critical path to the headline (★ = real walls)
| Step | What | Status |
|---|---|---|
| **A** Boundedness Thm 5.4 | crux | ✅ DONE lap 14 |
| **B** Corollary `‖≺‖≤2^β` | invert TI + Boundedness | ✅ DONE lap 14 |
| **C₁** `XFreeAx` cutElim → cr=0 | the big §19 port | ✅ DONE lap 15 |
| **D** Thm 5.6 tail | C₁ ∘ B | ✅ DONE lap 15 (`orderType_le_of_TIprovable`) |
| **C₂-crux** X-induction meta-induction + LX-EM | faithfulness-critical | ✅ DONE lap 15 (`metaInduction`, `provable_em_x`) |
| **C₂-struct** `embedC_LX_gen` structural port | 9/10 cases | ✅ **DONE lap 16** (`exs` = the wall below) |
| **C₂-axLv** value-congruent literal axiom | the `exs` wall — a calculus retrofit | ✅ **LANDED lap 16** across 3 files; 1 disclosed `sorry` (`atomCut_x` X-atom-cut) pending `nrel_value_subst` |
| **C₂-axm** discharge `hax` for `paLX` | X-free via `provable_true_x` + X-ind via `metaInduction` glue | not started |
| **E** Goodstein⟹TI_≺(X) bridge | Kirby–Paris; reuse Phase-0 CNF-ε₀ | not started |
| **F ★** Arithmetization seam | ℒₒᵣ-def ε₀ order, `‖≺‖=ε₀`, discharge `hprec`/`hprecXPos` | not started — 2nd hard wall |
| **G** Final assembly | chain + `#print axioms` clean | not started |

## ✅ Lap-16 (cont.): the `axLv` retrofit LANDED (build green, 1266) — ONE disclosed `sorry` remains
The value-congruent literal axiom `Deriv.axLv (r) (v v') (hval) …` (Buchholz `AX(Z∞)` p.27, generic
over `L`) is threaded through all three files:
- **`ZinftyGen`** — constructor + `o`/`cr` + `Provable.axLv` + `litTrue_rel_congr`; all 8 sites incl.
  the **`atomCutAux`** value-cong literal-cut (truth-split: `removeFalseLit` on the `hNC` side when the
  cut atom is true, `axTrue` on the value-cong negative when false) and the **3-case
  `removeFalseLitAux`** — green, axiom-clean (generic, no XFreeAx constraint).
- **`Boundedness`** — `XFreeAx` `axLv` leaf (`True`); the 3 `_xfree` inversions; main `boundedness`
  induction **case 1.2** generalised to the value-cong X-pair (`tval va = tval vb` via `hval`).
- **`XFreeCutElim`** — `PXFc.axLv` + 7/8 `_x` sites. **The 1 remaining `sorry`:** `PXFc.atomCutAux`'s
  value-cong **X-atom-cut** case (`XFreeCutElim.lean:1048`); at an X-atom cut `axTrue` is forbidden, so
  the value-cong negative must be transported via a renaming lemma (below).

⚠️ **C₁/D carry this one disclosed `sorry`** (`PXFc.cutElim`, `orderType_le_of_TIprovable`) — honest WIP
of the calculus generalisation; clears to axiom-clean the instant the lemma below lands.

## NEXT (lap 17): `nrel_value_subst` → clears `atomCut_x` → `exs` → `embedC_LX`
1. **`PXFc.nrel_value_subst`** (the one lemma): `Δ` cut-free `XFreeAx`, `nrel r v ∈ Δ`, `|v|=|w|` ⟹
   `PXFc d.o 0 (insert (nrel r w) (Δ.erase (nrel r v)))`. **Structure = `removeFalseLitAux_x` with the
   frame `Γ.erase Lit` → `insert Lit' (Γ.erase Lit)`** (`Lit = nrel r v`, `Lit' = nrel r w`); compound
   cases are the same incidental recursion. **Leaves:** at an `axL`/`axLv` whose negative IS `nrel r v`,
   pair the surviving positive with `Lit'` via `PXFc.axLv` (value-cong from `|v|=|w|`); at a true
   `axTrue` literal `= nrel r v` (X-free), re-emit `axTrue` on `nrel r w`; else re-emit unchanged.
   **Watch:** the matched `axLv` leaf needs `r₀=r` + a value extraction from `nrel rr vv = nrel r vb` —
   use `congrArg (∼·)` (→ `rel rr vv = rel r vb`) instead of raw dependent `injection`. Then `atomCut_x`
   Case `hrel`: transport `hNC` by `nrel_value_subst` into `result` — uniform, no truth split, no X-`axTrue`.
2. **`exs` discharge** (`EmbeddingX.lean:203`): `litTrue_subst_congr` + `provable_em_cong_gen_x`
   (value-cong EM over `LX`: X-atoms via `axLv`, X-free via `axTrue`) ⟹ `PXFc.exI_closed` ⟹ kills `exs`.
3. **`embedC_LX`** = `embedC_LX_gen` at `𝓢 := ↑paLX` once `hax` proven. Then **D fires** ⟹ Thm 5.6.

## Then (after C₂-struct is sorry-free): C₂-axm + the statement `embedC_LX`
- Define `paLX : Theory LX := Theory.lMap (Language.ORing.embedding LX) 𝗣𝗔⁻ + InductionScheme LX Set.univ`
  (this RESOLVES "what is `Z ⊢ TI(X)`": `Derivation2 (↑paLX) {TI prec}`; `InductionScheme L` IS generic
  over an ORing `L` — confirmed). Then `embedC_LX := embedC_LX_gen` with `𝓢 := ↑paLX` once `hax` is
  proven: **X-free axioms** (`lMap`-image of `𝗣𝗔⁻` + X-free induction instances) via `provable_true_x`
  (need lMap⟹X-free + true-in-ℕ lemmas); **X-induction instances** via `metaInduction` (the Foundation-
  DSL glue: build `step` from `ψ` by the successor substitution, prove `hstep`, strip `univCl`+the two
  `🡒`). Deliverable `embedC_LX : (↑paLX ⊢₂ {TI prec}) → ∃ c α, PXFc α c {TI prec}` ⟹ **D fires** ⟹ Thm 5.6.

## Notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `sorry`.
- **Aristotle:** idle. The cleanly-feedable open lemmas all need either the `axLv` retrofit (exs) or
  large `LX`/`PXFc` context (metaInduction glue), so it stayed correctly idle this lap.
- **Banked off-path (do NOT resume):** witness-bounded `wip/` calculi; `Zᵏ`/M6.
- Build: `lake build GoodsteinPA` (1266). Axiom ledger in `STATUS.md`.
